#!/usr/bin/env python3
"""Export and classify proof dependencies from the compiled Lean environment.
Run --prepare, lake env lean _out/audit/Environment.lean, then run with no options.
Source inventory supplies names only; proof status comes from Lean, not a sorry regex.
"""
from pathlib import Path
import argparse,json,re,hashlib,subprocess
from collections import Counter
from blueprint_associations import namespace_at
from blueprint_source import ROOT,read_project
from statement_registry import PARTIAL_COVERAGE
OUT=ROOT/'_out/audit'
OUT.mkdir(parents=True,exist_ok=True)
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--prepare',action='store_true');args=p.parse_args()
pattern=re.compile(r'^(?:@\[[^\]]+\]\s*)*(?:(?:noncomputable|private|protected)\s+)*(def|theorem|lemma|structure|abbrev|inductive)\s+([^\s(:]+)',re.M)
inventory={}
source_digest=hashlib.sha256()
for path in sorted((ROOT/'WPFormalization').rglob('*.lean')):
    text=path.read_text()
    source_digest.update(str(path.relative_to(ROOT)).encode());source_digest.update(text.encode())
    for m in pattern.finditer(text):
        # Private implementation constants are reached by graph traversal, not guessed names.
        if 'private ' in m[0]:continue
        # Lean's explicit _root_ escape resets the namespace. These authored
        # generic helpers are project constants even outside the WP namespace.
        explicit_root=m[2].startswith('_root_.')
        name=m[2][len('_root_.'):] if explicit_root else namespace_at(text,m.start())+'.'+m[2]
        if not name.startswith('WP.') and not explicit_root:continue
        if name in inventory:raise SystemExit('Duplicate authored declaration: '+name+' in '+inventory[name]['path']+' and '+str(path.relative_to(ROOT)))
        inventory[name]={'path':str(path.relative_to(ROOT)),'kind':m[1]}
if args.prepare:
    code='''import WPFormalization.Statements
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def projectConstant (n : Name) : Bool :=
  n.toString.startsWith "WP." || n.toString.startsWith "_private.WPFormalization."

-- Direct named paper-goal premises are tracked independently of the conclusion.
-- These formerly open goals now have actual producers; the exact examples
-- below are kernel-checked again on every fresh export.
example (P : WP.PsiTheory) : WP.HigherOrder.UniformRecursiveRemainderTarget P :=
  WP.HigherOrder.canonical_uniform_recursive_remainders P
example (P : WP.PsiTheory) : WP.HigherOrder.CanonicalAdjacentCompatibility P :=
  WP.HigherOrder.canonical_adjacent_compatibility P
example (P : WP.PsiTheory) : WP.HigherOrder.KernelFiniteData.PolynomialDependenceTarget P :=
  WP.HigherOrder.KernelFiniteData.canonical_polynomial_dependence P
example (P : WP.PsiTheory) : WP.HigherOrder.KernelFiniteData.ProfileBoundaryPolynomialTarget P :=
  WP.HigherOrder.KernelFiniteData.canonical_profile_boundary_polynomial P
example (P : WP.PsiTheory) : WP.HigherOrder.UniformRecursiveExpansionsTarget P :=
  WP.uniform_recursive_expansions P
example (P : WP.PsiTheory) (J k : Nat) (hk : k ≤ J) :
    WP.HigherOrder.KernelFiniteData.FiniteDataStage P J k :=
  WP.HigherOrder.KernelFiniteData.canonical_finite_data_stage P J k hk
private partial def explicitPaperPremises (e : Expr) : Array Name :=
  match e with
  | .forallE _ domain body _ =>
    let here := domain.getUsedConstants.filter (fun n =>
      n.toString == "WP.HigherOrder.UniformRecursiveRemainderTarget" ||
      n.toString == "WP.HigherOrder.CanonicalAdjacentCompatibility" ||
      n.toString == "WP.HigherOrder.KernelFiniteData.PolynomialDependenceTarget" ||
      n.toString == "WP.HigherOrder.KernelFiniteData.ProfileBoundaryPolynomialTarget" ||
      n.toString == "WP.HigherOrder.UniformRecursiveExpansionsTarget")
    here ++ explicitPaperPremises body
  | .letE _ _ _ body _ => explicitPaperPremises body
  | _ => #[]

-- Record direct project edges, including generated/private implementation constants.
-- Python computes their closure; Lean independently supplies the transitive axiom set.
run_cmd do
  let env := (← getEnv).setExporting false
  let mut records : Array Json := #[]
  let all := env.constants.toList.filter (fun (n, _) => projectConstant n)
  for (n, info) in all do
    let refs := info.getUsedConstantsAsSet.toArray.filter projectConstant
    let axs ← collectAxioms n
    let interfaces := info.type.getUsedConstants.filter (fun k =>
      k.toString == "WP.PsiTheory" || k.toString.startsWith "WP.External.")
    records := records.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("directSorry", toJson ((info.value? (allowOpaque := true)).any (·.hasSorry) || info.type.hasSorry)),
      ("axioms", toJson (axs.map Name.toString)),
      ("projectReferences", toJson (refs.map Name.toString)),
      ("typeInterfaces", toJson (interfaces.map Name.toString)),
      ("paperPremises", toJson ((explicitPaperPremises info.type).map Name.toString))]
  IO.FS.writeFile "_out/audit/environment.json" (Json.pretty (toJson records))
  logInfo m!"Exported {records.size} project constants, their direct proof gaps, interfaces, and transitive axioms."
'''
    root_helpers=sorted(n for n in inventory if not n.startswith('WP.'))
    # Include authored root helpers and their direct edges in the SAME compiled
    # export and transitive dependency analysis, rather than dropping them.
    root_test=' || '.join('n.toString == '+json.dumps(n) for n in root_helpers)
    if root_test:
        code=code.replace('n.toString.startsWith "WP." || n.toString.startsWith "_private.WPFormalization."',
            'n.toString.startsWith "WP." || n.toString.startsWith "_private.WPFormalization." || '+root_test)
    code=code.replace('(Json.pretty (toJson records))', '(Json.pretty (Json.mkObj [("sourceHash", toJson "'+source_digest.hexdigest()+'"), ("records", toJson records)]))')
    (OUT/'Environment.lean').write_text(code)
    (OUT/'source-inventory.json').write_text(json.dumps(inventory,ensure_ascii=False,indent=2)+'\n')
    print(f'Prepared Lean environment audit for {len(inventory)} authored declarations.')
    raise SystemExit
snapshot=json.loads((OUT/'environment.json').read_text())
if snapshot['sourceHash'] != source_digest.hexdigest():raise SystemExit('Source changed since compiled audit; rerun --prepare and Lean export.')
raw=snapshot['records'];env={x['name']:x for x in raw}
missing=inventory.keys()-env.keys()
if missing:raise SystemExit('Compiled declaration missing: '+', '.join(sorted(missing)))
external_inputs=json.loads((ROOT/'audit/external-inputs.json').read_text())
external_roots={n for x in external_inputs if x['status']=='EXTERNAL_SORRY' for n in x['lean'] if env.get(n,{}).get('directSorry')}
interfaces={n for x in external_inputs if x['status']=='EXPLICIT_INTERFACE' for n in x['lean']} | {'WP.External.PainleveAnalytic.GIKMData','WP.External.PainleveAnalytic.CCHData'}
standard={'propext','Classical.choice','Quot.sound'}
def closure(n):
    seen=set();todo=[n]
    while todo:
        k=todo.pop()
        if k in seen:continue
        seen.add(k);todo.extend(env.get(k,{}).get('projectReferences',[]))
    return seen
# Fresh Lean export checked the exact P-only types of the global producers above.
# Indexed FiniteDataStage is checked with k≤J, never blindly whitelisted by its head.
# Also require their complete gap/axiom closures to use only licensed classics.
proved_paper_goals={
    'WP.HigherOrder.UniformRecursiveRemainderTarget': 'WP.HigherOrder.canonical_uniform_recursive_remainders',
    'WP.HigherOrder.CanonicalAdjacentCompatibility': 'WP.HigherOrder.canonical_adjacent_compatibility',
    'WP.HigherOrder.KernelFiniteData.PolynomialDependenceTarget': 'WP.HigherOrder.KernelFiniteData.canonical_polynomial_dependence',
    'WP.HigherOrder.KernelFiniteData.ProfileBoundaryPolynomialTarget': 'WP.HigherOrder.KernelFiniteData.canonical_profile_boundary_polynomial',
    'WP.HigherOrder.UniformRecursiveExpansionsTarget': 'WP.uniform_recursive_expansions',
}
for goal,producer in proved_paper_goals.items():
    e=env.get(producer)
    roots={k for k in closure(producer) if env.get(k,{}).get('directSorry')}
    if not e or e.get('paperPremises') or roots-external_roots or set(e['axioms'])-standard-{'sorryAx'}:
        raise SystemExit('Invalid paper-goal producer: '+producer)
records={}
for n,source in inventory.items():
    e=env[n];c=closure(n);roots=sorted(k for k in c if env.get(k,{}).get('directSorry'))
    imported=sorted(set(k for r in c for k in env.get(r,{}).get('typeInterfaces',[])) & interfaces)
    unknown=set(e['axioms'])-standard-{'sorryAx'}
    unresolved_paper_premises=sorted(set(e.get('paperPremises',[]))-proved_paper_goals.keys())
    incomplete=bool(unresolved_paper_premises or set(roots)-external_roots or unknown or ('sorryAx' in e['axioms'] and not roots))
    state='INCOMPLETE' if incomplete else ('EXTERNAL_DEFERRED' if n in external_roots or source['kind']=='structure' and n in interfaces else ('CONDITIONAL' if imported or roots else 'VERIFIED'))
    records[n]={**source,**e,'sorryRoots':roots,'externalInterfaces':imported,'unexpectedAxioms':sorted(unknown),'status':state,'unresolvedPaperPremises':unresolved_paper_premises}
nodes,rows,*_=read_project();target_records=[]
for r in rows:
    ds=[records[n] for n in r['associations']]
    isext=r['classification'].startswith('external-')
    if r['label'] in PARTIAL_COVERAGE:status='BLOCKED' if isext else 'INCOMPLETE'
    elif not ds:status='BLOCKED'
    elif any(d['status']=='INCOMPLETE' for d in ds):status='INCOMPLETE'
    # A library-backed proof is verified even when its Blueprint node was
    # originally an external candidate. Only unproved classical inputs defer.
    elif isext:status='VERIFIED' if all(d['status']=='VERIFIED' for d in ds) else 'EXTERNAL_DEFERRED'
    elif any(d['status'] in ('CONDITIONAL','EXTERNAL_DEFERRED') for d in ds):status='CONDITIONAL'
    else:status='VERIFIED'
    target_records.append({'label':r['label'],'number':r['number'],'classification':r['classification'],'status':status,'declarations':r['associations'],'partialCoverage':PARTIAL_COVERAGE.get(r['label'])})
counts=Counter(r['status'] for r in target_records)
new=Counter(r['status'] for r in target_records if r['classification']=='paper-new')
open_paper_targets=[r['label'] for r in target_records if r['classification']=='paper-new'
                    and r['status'] not in ('VERIFIED','CONDITIONAL')]
core_status='INCOMPLETE' if open_paper_targets else 'CLOSED_CONDITIONALLY'
report={'sourceHash':source_digest.hexdigest(),'overallStatus':'INCOMPLETE',
        'stage1CoreProofStatus':core_status,'remainingPaperTargets':open_paper_targets,
        'unconditionalProjectStatus':'INCOMPLETE_EXTERNAL_DEPENDENCIES',
        'targets':len(nodes),'targetCounts':dict(counts),'paperNewCounts':dict(new),'externalSorryRoots':sorted(external_roots),'provedPaperGoalProducers':proved_paper_goals,'declarations':records,'targetRecords':target_records}
(OUT/'proof-status.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
expected=json.loads((ROOT/'audit/summary.json').read_text())
assert dict(counts)==expected['targetCounts'],('target status drift',dict(counts))
assert dict(new)==expected['paperNewCounts'],('paper-new status drift',dict(new))
assert len(external_roots)==expected['externalSorryRoots']
assert len(records)==expected['authoredDeclarations']
assert core_status==expected['stage1CoreProofStatus']
print(json.dumps({'targets':len(nodes),'counts':dict(counts),'paperNew':dict(new),'authoredDeclarations':len(records),'externalSorryRoots':len(external_roots)},ensure_ascii=False))
