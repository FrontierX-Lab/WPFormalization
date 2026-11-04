"""Read the explicit blueprint string attributes used by this project's Lean modules.

Handles multiple labels and namespace qualification. Fail closed on unsupported
attribute options; compiled environment/preview checks remain authoritative.
"""
import re

PATTERN = re.compile(
    r'(?P<attrs>(?:@\[[^\]]+\]\s*)+)'
    r'(?:(?:noncomputable|private|protected)\s+)*'
    r'(?P<kind>def|theorem|lemma|abbrev|structure|inductive)\s+(?P<name>[^\s(:]+)')


def namespace_at(text, offset):
    scopes = []
    for line in text[:offset].splitlines():
        if m := re.fullmatch(r'namespace\s+(\S+)\s*', line):
            scopes.append(('namespace', m[1]))
        elif m := re.fullmatch(r'(?:noncomputable\s+)?section(?:\s+(\S+))?\s*', line):
            scopes.append(('section', m[1]))
        elif m := re.fullmatch(r'end(?:\s+(\S+))?\s*', line):
            if not scopes:
                raise ValueError('Unmatched scope end')
            if m[1] and scopes[-1][1] != m[1]:
                raise ValueError('Ambiguous namespace scope: ' + line)
            scopes.pop()
    return '.'.join(name for kind, name in scopes if kind == 'namespace')


def attributed_declarations(text):
    for match in PATTERN.finditer(text):
        blocks = re.findall(r'@\[([^\]]+)\]', match['attrs'])
        labels = []
        for block in blocks:
            if 'blueprint' not in block:
                continue
            labels.extend(re.findall(r'blueprint\s+"([^"]+)"', block))
            residue = re.sub(r'blueprint\s+"[^"]+"', '', block)
            if residue.strip(' ,\n\t'):
                raise ValueError('Unsupported blueprint attribute options: ' + block)
        if not labels:
            continue
        prefix = namespace_at(text, match.start())
        name = match['name']
        if prefix and not name.startswith(prefix + '.'):
            name = prefix + '.' + name
        yield {'name': name, 'labels': labels, 'kind': match['kind'],
               'start': match.start(), 'end': match.end()}
