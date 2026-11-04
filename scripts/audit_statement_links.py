#!/usr/bin/env python3
"""Audit compiled Blueprint via official vbp query (not by counting source labels).
Run after lake build && lake exe vbp build. JSON shapes are pinned to this project's vbp revision.
"""
from pathlib import Path
import json, subprocess, concurrent.futures, collections, argparse
from blueprint_source import read_project
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'_out/audit'
OUT.mkdir(parents=True,exist_ok=True)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--prefix',default='compiled')
args=parser.parse_args()
source_nodes, *_ = read_project()
CLI=ROOT/'.lake/packages/VersoBlueprint/.lake/build/bin/vbp'
registry=json.loads((ROOT/'audit/statement-registry.json').read_text())
def query(*args):
    p=subprocess.run([str(CLI),'query',*args],cwd=ROOT,text=True,capture_output=True,check=True)
    return json.loads(p.stdout)
labels=query('labels')
queue=query('work-queue')
metadata=query('metadata')
for name,data in [('labels',labels),('work-queue',queue),('metadata',metadata)]:
    (OUT/f'{args.prefix}-{name}.json').write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
def audit_node(r):
    node=query('node',r['label'])
    actual=node.get('leanCodePreviewKeys',[])
    authored=source_nodes[r['label']]
    for axis in ['statementUses','proofUses']:
        assert {d['label'] for d in node[axis]}==set(authored[axis]),('compiled dependency drift',r['label'],axis)
    external=(node.get('codeData') or {}).get('externalDecls',[])
    canonical={d['canonical'] for d in external}
    assert canonical=={d['name'] for d in r['declarations']},('wrong compiled declaration',r['label'],canonical)
    assert all(d['present'] for d in external),('missing declaration',r['label'])
    assert all(d['origin']=='blueprintAttr' for d in external),('association is not an attribute',r['label'])
    assert all(d.get('render',{}).get('ok',{}).get('html') for d in external),('failed declaration HTML',r['label'])
    for d in external:
        wanted=next(x for x in r['declarations'] if x['name']==d['canonical'])
        if wanted['directSorry']:
            assert 'containsSorry' in str(d['provedStatus']),(r['label'],d)
    if r['associated']:
        assert actual,('missing compiled association',r['label'])
    else:
        assert not actual,('unexpected compiled association',r['label'],actual)
    return {'label':r['label'],'previewKeys':actual}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    nodes=list(pool.map(audit_node,registry))
expected=collections.defaultdict(set)
for r in registry:
    for d in r['declarations']:expected[d['name']].add(r['label'])
declarations=list(expected)
# A theorem with a direct sorry must never be reported locally proved.
q={e['label']:e for e in queue['entries']}
for r in registry:
    if any(d['kind'] in ['theorem','lemma'] and d['directSorry'] for d in r['declarations']):
        if r['label'] not in q:
            # work-queue omits nonactionable definition nodes blocked by dependencies.
            continue
        assert q[r['label']]['proofStatus']=='Lean code incomplete',(r['label'],q[r['label']])
        # The queue is actionable-only, not a complete node status table.
        # Definition nodes also count proof gaps against their statement stage.
        if q[r['label']]['kind'] != 'definition':
            assert q[r['label']]['statementStatus']=='formalized',(r['label'],q[r['label']])
report={'targets':len(registry),'associatedTargets':sum(r['associated'] for r in registry),
        'distinctCompiledDeclarations':len(declarations),'blocked':sum(not r['associated'] for r in registry),
        'queueEntries':len(q),'queueProofStatusCounts':dict(collections.Counter(e['proofStatus'] for e in q.values())),
        'compiledAssociationErrors':0,'falseProofCompletions':0,'associationMechanism':'blueprintAttr',
        'scope':'Checks compiled associations/proof status; semantic fidelity and explicit interface assumptions remain separately audited.'}
(OUT/f'{args.prefix}-link-audit.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(report,ensure_ascii=False,indent=2))
