"""Read frozen Blueprint sources; no documentation or source writes."""
from pathlib import Path
from collections import Counter, defaultdict
from blueprint_associations import attributed_declarations
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
BEGIN = '<!-- BEGIN GENERATED FORMALIZATION DATA -->'
END = '<!-- END GENERATED FORMALIZATION DATA -->'
KINDS = 'definition|lemma_|proposition|theorem|corollary|proof'
ROOTS = ['thm:intro-absolute', 'cor:constant', 'thm:volume', 'thm:coefficient',
         'thm:chain', 'cor:spectral', 'thm:absolute', 'thm:pants-poisson',
         'cor:many-spectrum', 'thm:tight-spectrum', 'cor:tight-boltzmann',
         'thm:critical-cluster']
CLASS = {'paper-new': 'Paper results and derivations to formalize', 'paper-definition': 'Paper definitions and conventions',
         'external-known': 'Known external results (exact interfaces require review)',
         'external-candidate': 'Infrastructure or sources requiring verification'}


def code(s):
    return '`' + s + '`'


def list_code(xs):
    return ', '.join(code(x) for x in sorted(xs)) or 'None'


def math_markdown(text):
    text = re.sub(r'\$\$`(.*?)`', lambda m: '\n\n$$\n' + m[1] + '\n$$\n\n', text, flags=re.S)
    text = re.sub(r'\$`(.*?)`', lambda m: '$' + m[1] + '$', text, flags=re.S)
    text = re.sub(r'\{bpref "([^"]+)"\}\[([^\]]*)\]',
                  lambda m: '[' + (m[2] or m[1]) + '](#target-' + m[1] + ')', text)
    return text.strip()


def read_project():
    old = {x['label']: x for x in json.loads((ROOT / 'audit/targets.json').read_text())}
    nodes, proofs = {}, {}
    start = re.compile(r'^:::(' + KINDS + r') "([^"]+)"([^\n]*)\n', re.M)
    for path in sorted((ROOT / 'WPBlueprint/Chapters').glob('*.lean')):
        text = path.read_text()
        for m in start.finditer(text):
            end = re.search(r'^:::\s*$', text[m.end():], re.M)
            if end is None:
                raise ValueError(f'Unclosed node {m[2]}')
            body = text[m.end():m.end() + end.start()]
            opts = m[3]
            uses = re.search(r'\(uses := "([^"]*)"\)', opts)
            uses = [s.strip() for s in uses[1].split(',')] if uses else []
            kind, label = m[1], m[2]
            rec = {'label': label, 'kind': kind, 'uses': uses, 'body': body,
                   'path': path.relative_to(ROOT).as_posix(),
                   'line': text[:m.start()].count('\n') + 1}
            if kind == 'proof':
                if label in proofs:
                    raise ValueError('Duplicate proof: ' + label)
                proofs[label] = rec
                continue
            if label in nodes:
                raise ValueError('Duplicate statement: ' + label)
            tags = re.search(r'\(tags := "([^"]*)"\)', opts)
            tags = [t.strip() for t in tags[1].split(',')] if tags else []
            classification = next((t for t in tags if t in CLASS), 'Auxiliary result (classification pending)')
            meta = re.match(r'%%%\n(.*?)\n%%%\s*', body, re.S)
            if meta:
                rec['pages'] = re.findall(r'page := "([^"]+)"', meta[1])
                rec['citations'] = re.findall(r'citation := "([^"]+)"', meta[1])
                rec['body'] = body[meta.end():].strip()
            else:
                rec['pages'], rec['citations'] = [], []
            initial = old.get(label, {})
            rec['classification'] = classification
            rec['title'] = initial.get('title', label)
            rec['number'] = initial.get('number', 'Unnumbered / source pending')
            heading = re.match(r'(?:Definition|Lemma|Theorem|Proposition|Corollary) (\S+) — (.+)\.\s*$', rec['body'].split('\n', 1)[0])
            if heading:
                if initial and initial['number'] != heading[1]:
                    raise ValueError('Source/initial-extraction numbering mismatch: ' + label)
                rec['number'], rec['title'] = heading[1], heading[2]
            rec['numbered'] = bool(label.startswith(('thm:', 'lem:', 'cor:', 'prop:')) and re.fullmatch(r'(?:\d+|[A-G])\.\d+', rec['number']))
            rec['statementUses'] = uses
            match = re.search(r'\(lean := "([^"]*)"\)', opts)
            rec['associations'] = [s.strip() for s in match[1].split(',')] if match else []
            rec['registered'] = bool(initial)
            nodes[label] = rec
    for label in proofs:
        if label not in nodes:
            raise ValueError('Proof without statement: ' + label)
    for label, rec in nodes.items():
        rec['proofUses'] = proofs.get(label, {}).get('uses', [])
        rec['deps'] = set(rec['statementUses'] + rec['proofUses'])
        if rec['deps'] - nodes.keys():
            raise ValueError(f'Dangling edges: {label}: {rec["deps"] - nodes.keys()}')
    # Scan declaration associations in ordinary local modules. Names are source
    # spellings, not a substitute for elaborated declaration/axiom inspection.
    lean_paths = sorted({*ROOT.glob('*.lean'), *ROOT.glob('WPFormalization/**/*.lean'),
                         *ROOT.glob('WPBlueprint/**/*.lean'), *ROOT.glob('audit/checks/*.lean')})
    declarations = []
    for path in lean_paths:
        text = path.read_text()
        for decl in attributed_declarations(text):
            for label in decl['labels']:
                if label not in nodes:
                    raise ValueError('Unknown attributed label: ' + label)
                nodes[label]['associations'].append(decl['name'])
        for m in re.finditer(r'^(?:(?:noncomputable|private|protected)\s+)*'
                             r'(def|theorem|lemma|axiom|opaque|abbrev|structure|inductive)\s+([^\s(:]+)', text, re.M):
            declarations.append((path.relative_to(ROOT).as_posix(), m[1], m[2]))
        # Fail closed on unsupported inline or implicit attribute associations.
        if re.search(r'^```lean\b', text, re.M) or re.search(r'@\[blueprint\s*(?:\]|\()', text):
            raise ValueError(f'Extend association parsing for inline/bare blueprint code in {path}')
    for rec in nodes.values():
        rec['associations'] = sorted(set(rec['associations']))
    order = re.findall(r'\{include 0 WPBlueprint\.Chapters\.([^}\s]+)\}',
                       (ROOT / 'WPBlueprint/Blueprint.lean').read_text())
    rank = {f'WPBlueprint/Chapters/{name}.lean': i for i, name in enumerate(order)}
    rows = sorted(nodes.values(), key=lambda x: (rank.get(x['path'], 999), x['line']))
    return nodes, rows, lean_paths, declarations

