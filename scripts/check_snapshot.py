#!/usr/bin/env python3
"""Check frozen bytes, registry counts and published local Markdown links.
Use --clean on a delivery snapshot after removing .lake and _out.
This checks packaging and registered evidence, not mathematical semantics.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, re, urllib.parse, os
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--clean',action='store_true');args=p.parse_args()
errors=[]
manifest={}
for line in (ROOT/'audit/sources.sha256').read_text().splitlines():
 h,name=line.split('  ',1);manifest[name]=h
for name,h in manifest.items():
 path=ROOT/name
 if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=h:errors.append('frozen bytes: '+name)
math=sorted((ROOT/'WPFormalization').rglob('*.lean'))
frozen_paths={p.relative_to(ROOT).as_posix() for folder in ['WPFormalization','WPBlueprint'] for p in (ROOT/folder).rglob('*.lean')}
frozen_paths.update(['WPFormalization.lean','WPBlueprint.lean','WPBlueprintMain.lean','lakefile.toml','lean-toolchain','lake-manifest.json'])
if frozen_paths != manifest.keys():errors.append('frozen inventory changed')
r=json.loads((ROOT/'audit/summary.json').read_text())
digest=hashlib.sha256()
for path in math:digest.update(path.relative_to(ROOT).as_posix().encode());digest.update(path.read_bytes())
if digest.hexdigest()!=r['sourceHash']:errors.append('mathematical digest changed')
if len(math)!=r['mathFiles']:errors.append('mathematical file count changed')
status=json.loads((ROOT/'audit/proof-status.json').read_text())
licenses=json.loads((ROOT/'audit/external-inputs.json').read_text())
if Counter(x['status'] for x in status['targetRecords'])!=r['targetCounts']:errors.append('target statuses')
if Counter(x['status'] for x in status['targetRecords'] if x['classification']=='paper-new')!=r['paperNewCounts']:errors.append('paper-new statuses')
if Counter(x['status'] for x in licenses)!= {'EXPLICIT_INTERFACE':50,'EXTERNAL_SORRY':27}:errors.append('license groups')
if len(status['externalSorryRoots'])!=r['externalSorryRoots']:errors.append('sorry roots')
target_text=(ROOT/'docs/TARGETS.md').read_text()
anchors=re.findall(r'<a id="target-([^"]+)"',target_text)
paper_records=[x for x in status['targetRecords'] if x['classification'] in ('paper-new','paper-definition')]
if len(anchors)!=len(paper_records) or set(anchors)!={x['label'] for x in paper_records}:errors.append('paper target table coverage')
for row in paper_records:
 for name in row['declarations']:
  if '['+name+'](' not in target_text:errors.append('formal declaration missing: '+name)
classic_ids=re.findall(r'<a id="input-([^"]+)"',(ROOT/'docs/CLASSICAL_RESULTS.md').read_text())
task_ids=re.findall(r'<a id="task-([^"]+)"',(ROOT/'docs/INFRASTRUCTURE.md').read_text())
expected_ids={x['id'].lower() for x in licenses}
if len(classic_ids)!=len(licenses) or set(classic_ids)!=expected_ids:errors.append('classical result list coverage')
if len(task_ids)!=len(licenses) or set(task_ids)!=expected_ids:errors.append('foundation task coverage')
if {p.name for p in (ROOT/'docs').glob('*.md')}!={'TARGETS.md','CLASSICAL_RESULTS.md','INFRASTRUCTURE.md'}:errors.append('unexpected reader document')
if hashlib.sha256((ROOT/'source/paper.pdf').read_bytes()).hexdigest()!=r['pdfSHA256']:errors.append('PDF hash')
# Ignore code and TeX math when recognizing Markdown links.
def prose(s):
 s=re.sub(r'```.*?```','',s,flags=re.S)
 s=re.sub(r'`[^`]*`','',s)
 s=re.sub(r'\$\$.*?\$\$','',s,flags=re.S)
 s=re.sub(r'(?<!\\)\$(?:\\.|[^$\n])*?(?<!\\)\$','',s)
 return s
links=0
for path in [ROOT/'README.md',*sorted((ROOT/'docs').rglob('*.md')),*sorted((ROOT/'audit').rglob('*.md'))]:
 text=path.read_text()
 if path==ROOT/'README.md' or path.is_relative_to(ROOT/'docs'):
  if '/root/Formalization/' in text:errors.append('absolute workspace path: '+str(path.relative_to(ROOT)))
  if 'WPFormalization_stage1' in text:errors.append('staging name in public docs: '+str(path.relative_to(ROOT)))
 for m in re.finditer(r'\[[^\]\n]*\]\(([^\s)]+)\)',prose(text)):
  url=m[1].strip('<>')
  if re.match(r'^[a-zA-Z]+:',url):continue
  name,_,fragment=url.partition('#');name=urllib.parse.unquote(name)
  dest=(path.parent/name).resolve() if name else path
  links+=1
  if not dest.is_relative_to(ROOT) or not dest.exists():errors.append(f'link {path.relative_to(ROOT)} -> {url}')
  elif fragment and dest.suffix=='.md' and ('id="'+urllib.parse.unquote(fragment)+'"') not in dest.read_text():errors.append(f'anchor {path.relative_to(ROOT)} -> {url}')
  elif fragment and dest.suffix=='.lean' and re.fullmatch(r'L[0-9]+',fragment):
   if not 1<=int(fragment[1:])<=len(dest.read_text().splitlines()):errors.append(f'source line {path.relative_to(ROOT)} -> {url}')
if set(p.name for p in ROOT.glob('*.md'))!={'README.md'}:errors.append('old root documents')
if args.clean:
 for base,dirs,files in os.walk(ROOT):
  for d in dirs:
   if d in ('.lake','_out','.git','__pycache__'):errors.append('forbidden directory: '+str((Path(base)/d).relative_to(ROOT)))
  for f in files:
   if f.endswith(('.log','.log.gz','.tar.gz','.olean','.ilean','.pyc','.c','.o','.trace','.prof')) or f=='.DS_Store':errors.append('forbidden artifact: '+str((Path(base)/f).relative_to(ROOT)))
print(json.dumps({'ok':not errors,'frozenFiles':len(manifest),'mathematicalFiles':len(math),'paperTargets':len(anchors),'blueprintTargets':len(status['targetRecords']),'licenseGroups':len(licenses),'externalSorryRoots':len(status['externalSorryRoots']),'localLinksChecked':links,'cleanDeliveryCheck':args.clean,'errors':errors},ensure_ascii=False,indent=2))
raise SystemExit(bool(errors))
