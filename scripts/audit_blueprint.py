#!/usr/bin/env python3
"""Audit authored labels/edges, not mathematical truth or Lean completeness."""
from pathlib import Path
import json,re,collections
root=Path(__file__).resolve().parents[1]
statements={};proofs=collections.defaultdict(list)
for path in sorted((root/'WPBlueprint/Chapters').glob('*.lean')):
 text=path.read_text()
 for m in re.finditer(r'^:::(definition|lemma_|proposition|theorem|corollary|proof) "([^"]+)"([^\n]*)',text,re.M):
  kind,label,opts=m.groups();deps=[]
  match=re.search(r'\(uses := "([^"]*)"\)',opts)
  if match:deps=[s.strip() for s in match[1].split(',') if s.strip()]
  meta=re.match(r'\n%%%\n(.*?)\n%%%',text[m.end():],re.S)
  pages=re.findall(r'page := "([^"]+)"',meta[1]) if meta else []
  rec={'kind':kind,'path':str(path.relative_to(root)),'uses':deps,'sourcePages':pages}
  if kind=='proof':proofs[label].append(rec)
  else:
   assert label not in statements,('duplicate statement',label)
   statements[label]=rec
expected=json.loads((root/'audit/targets.json').read_text())
assert set(statements)=={r['label'] for r in expected},('coverage mismatch',set(statements)^{r['label'] for r in expected})
for label,rs in proofs.items():
 assert label in statements,('proof lacks statement',label)
 assert len(rs)==1,('duplicate proof',label)
edges={label:set(r['uses'])|set(d for p in proofs[label] for d in p['uses']) for label,r in statements.items()}
for label,ds in edges.items():
 assert label not in ds,('self edge',label)
 assert ds<=statements.keys(),('dangling dependency',label,ds-statements.keys())
seen=set();stack=[]
def visit(label):
 assert label not in stack,('cycle',stack+[label])
 if label in seen:return
 stack.append(label)
 for d in edges[label]:visit(d)
 stack.pop();seen.add(label)
for k in edges:visit(k)
for p in (root/'WPBlueprint').rglob('*.lean'):
 for ref in re.findall(r'\{bpref "([^"]+)"',p.read_text()):assert ref in statements,('dangling bpref',ref,p)
numbered=[r for r in expected if r['label'].startswith(('lem:','thm:','prop:','cor:'))]
assert len(numbered)==57
pdfpages=(root/'source/paper.txt').read_text().split('\f')
for r in numbered:
 assert str(r['page']) in statements[r['label']]['sourcePages'],('Blueprint source-page mismatch',r['label'],statements[r['label']]['sourcePages'],r['page'])
 pattern=r'^[ \t]*'+r['kind'].title()+r'\s+'+re.escape(r['number'])+r'(?=\s*(?:[.(]|$))'
 assert re.search(pattern,pdfpages[r['page']-1],re.M),('PDF provenance mismatch',r['label'],r['page'])
report={'nodes':len(statements),'numberedPaperResults':len(numbered),'statementEdges':sum(len(r['uses']) for r in statements.values()),'proofEdges':sum(len(p['uses']) for ps in proofs.values() for p in ps),'cycles':0,'danglingReferences':0,'duplicateLabels':0,'classification':dict(collections.Counter(r['classification'] for r in expected)),'scope':'Structural and PDF-start-page checks only; no mathematical completeness claim.'}
(root/'audit/coverage.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(report,ensure_ascii=False,indent=2))
