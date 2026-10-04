#!/usr/bin/env python3
"""Fresh source-only compilation. Never build, clean, or write third-party/baseline caches."""
from pathlib import Path
import concurrent.futures as cf
import datetime,hashlib,json,os,re,subprocess,sys,time,traceback
if not __debug__ or sys.flags.optimize:
 raise SystemExit('Optimized Python disables verification guards; rerun without -O/PYTHONOPTIMIZE')
root=Path(__file__).resolve().parent.parent
os.chdir(root)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
label=sys.argv[1] if len(sys.argv)>1 else 'current'
assert re.fullmatch(r'[\w.-]+',label), 'Invalid run label'
snapshot=subprocess.check_output([sys.executable,'scripts/snapshot.py'],text=True)
snapshot_id=hashlib.sha256(snapshot.encode()).hexdigest()
run=root/'logs/runs'/f'{snapshot_id}-{label}'
if run.exists(): raise SystemExit(f'Refusing to overwrite existing verification run {run}')
run.mkdir(parents=True)
run_started=time.monotonic()
def fail_preflight(exc_type,error,tb):
 # Uncaught setup failures have terminal evidence just like compile failures.
 state=globals().get('summary',{'snapshot':snapshot_id,'run_label':label})
 state.update(status='FAILED',exit=130 if exc_type is KeyboardInterrupt else 1,error=str(error),elapsed_seconds=round(time.monotonic()-run_started,3))
 (run/'summary.json').write_text(json.dumps(state,indent=2)+'\n')
 (run/'verify.exit').write_text(str(state['exit'])+'\n')
 sys.__excepthook__(exc_type,error,tb)
sys.excepthook=fail_preflight
(run/'source-snapshot.sha256').write_text(snapshot)
build=run/'build';build.mkdir()
dependency_root=Path(os.environ.get('PLGH_DEPENDENCY_ROOT',str(root/'.lake/packages'))).resolve()
manifest=json.loads((root/'lake-manifest.json').read_text())
dependencies=[];dependency_evidence=[]
for package in manifest['packages']:
 directory=dependency_root/package['name']; artifacts=directory/'.lake/build/lib/lean'
 rev=subprocess.check_output(['git','--no-optional-locks','-C',str(directory),'rev-parse','HEAD'],text=True).strip()
 if rev!=package['rev']:raise RuntimeError(f'Dependency revision mismatch: {package["name"]}')
 dirty=subprocess.check_output(['git','--no-optional-locks','-C',str(directory),'status','--porcelain','--untracked-files=no'],text=True)
 if dirty:raise RuntimeError(f'Tracked dependency source modified: {package["name"]}')
 for forbidden in ['PlanarHom','PlanarHom.olean','scripts','scripts.olean','Audit','Audit.olean']:
  if (artifacts/forbidden).exists():raise RuntimeError(f'Project artifact shadowing in dependency cache: {artifacts/forbidden}')
 if artifacts.is_dir():dependencies.append(artifacts)
 dependency_evidence.append({'name':package['name'],'expected_revision':package['rev'],'actual_revision':rev,'tracked_source_clean':True,'artifact_path':str(artifacts),'artifact_directory_present':artifacts.is_dir()})
(run/'dependency-pins.json').write_text(json.dumps(dependency_evidence,indent=2)+'\n')
env=os.environ.copy();env['LEAN_PATH']=str(build)+':'+':'.join(str(p) for p in dependencies)
env['LEAN_NUM_THREADS']='1'
(run/'LEAN_PATH.txt').write_text(env['LEAN_PATH']+'\n')
version=subprocess.check_output(['lean','--version'],text=True,env=env);(run/'toolchain.txt').write_text(version)
assert 'version 4.24.0' in version and '797c613eb9b6d4ec95db23e3e00af9ac6657f24b' in version,version
start=time.monotonic();results=[]
started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()

lean_stack_kib=65536
summary={'started_utc':started_utc,'status':'RUNNING','snapshot':snapshot_id,'source_only_project_recompile':True,'baseline_project_artifacts_reused':False,'third_party_artifacts':'read-only LEAN_PATH; no Lake dependency build invoked','toolchain':version.strip(),'run_label':label,'dependency_root':str(dependency_root),'dependency_pins_verified':len(dependency_evidence),'optional_origin_checks':os.environ.get('PLGH_VERIFY_ORIGINS')=='1','lean_thread_stack_kib':lean_stack_kib,'retained_fresh_compilations':0,'pre_campaign_project_cache_reused':False}
(run/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
# Accepted local hashes are mandatory; external absolute origins are optional.
protected={}
prov=json.loads((root/'SOURCE_PROVENANCE.json').read_text())
accepted={}
for r in prov['records']:
 path=Path(r['path'])
 if path.suffix in {'.lean','.py','.sh','.toml'} and path.parts[0] not in {'docs','paper'} or str(path) in {'lean-toolchain','lake-manifest.json'}:
  accepted[str(path)]=r['sha256']
 if os.environ.get('PLGH_VERIFY_ORIGINS')=='1':
  raise RuntimeError('Historical external origins are not build inputs; use the local source provenance and restoration receipt')
for r in prov['new_verification_support']:accepted[r['path']]=r['sha256']
actual_accepted={str(p.relative_to(root)) for p in (root/'PlanarHom').rglob('*.lean')}|{'PlanarHom.lean','lakefile.toml','lean-toolchain','lake-manifest.json'}
actual_accepted.update(str(p.relative_to(root)) for p in (root/'scripts').rglob('*') if p.is_file() and p.suffix in {'.lean','.py','.sh','.json'})
actual_accepted.update(str(p.relative_to(root)) for p in (root/'Audit').rglob('*') if p.is_file() and p.suffix in {'.lean','.json'})
assert set(accepted)==actual_accepted,f'Accepted source inventory mismatch: {set(accepted)^actual_accepted}'
for rel,digest in accepted.items():assert sha(root/rel)==digest,f'Accepted source hash mismatch: {rel}'
for directory in filter(None,os.environ.get('PLGH_EVIDENCE_ROOTS','').split(os.pathsep)):
 if not Path(directory).is_dir():raise RuntimeError(f'Explicit evidence root does not exist: {directory}')
 for p in Path(directory).rglob('*'):
  if p.is_file() and '__pycache__' not in p.parts:protected[str(p)]=sha(p)
(run/'external-source-guard-before.json').write_text(json.dumps(protected,indent=2)+'\n')
(run/'accepted-source-guard.log').write_text(f'PASS: {len(accepted)} accepted local source/tool/configuration hashes match provenance.\n')

def code_only(text):
 # Lean nested block comments, line comments and quoted strings are excluded.
 out=[];i=0;depth=0;string=False
 while i<len(text):
  if depth:
   if text.startswith('/-',i):depth+=1;i+=2
   elif text.startswith('-/',i):depth-=1;i+=2;out.append(' ')
   else:out.append('\n' if text[i]=='\n' else ' ');i+=1
  elif string:
   if text[i]=='\\':i+=2
   elif text[i]=='"':string=False;i+=1;out.append(' ')
   else:i+=1
  elif text.startswith('/-',i):depth=1;i+=2;out.append(' ')
  elif text.startswith('--',i):
   j=text.find('\n',i);i=len(text) if j<0 else j
  elif text[i]=='"':string=True;i+=1;out.append(' ')
  else:out.append(text[i]);i+=1
 return ''.join(out)
specification_files = {
 'Audit/Official/Challenge.lean': {'sorry'},
 'Audit/Official/NegativeAxiom.lean': {'axiom'},
}
isolated_modules = {'Audit.Official.Challenge', 'Audit.Official.NegativePremise',
                    'Audit.Official.NegativeAxiom'}
for rel in actual_accepted:
 if rel.endswith('.lean'):
  code=code_only((root/rel).read_text())
  tokens=set(re.findall(r'\b(sorry|admit|sorryAx|axiom)\b',code))
  forbidden=tokens-specification_files.get(rel,set())
  assert not forbidden,f'Forbidden unproved-source tokens in {rel}: {sorted(forbidden)}'
  if rel not in specification_files and rel!='Audit/Official/NegativePremise.lean':
   imports=set(re.findall(r'(?m)^\s*import\s+([\w.]+)',code))
   assert not imports & isolated_modules,f'Specification or negative control imported by proof code: {rel}'
suites=json.loads((root/'scripts/regression-suites.json').read_text())
gates=json.loads((root/'scripts/integration-gates.json').read_text())
assert len(suites)==len(set(suites)),'Duplicate regression suite entry'
for suite in suites:assert re.fullmatch(r'[A-Za-z0-9_]+',suite),f'Invalid suite name: {suite}'
audit_template=(root/'scripts/RegressionAxiomAudit.lean').read_text()
assert audit_template.count('-- PLGH_REGRESSION_IMPORT')==1,'Regression audit template must have exactly one import placeholder'
script_files={p.stem for p in (root/'scripts').glob('*.lean')}
expected_scripts=set(suites)|{'AxiomAudit','RegressionAxiomAudit','CompletedStatementScopeAudit'}|set(gates['named_axiom_audits'])
assert script_files==expected_scripts,f'Unclassified test/audit script files: {script_files^expected_scripts}'

def record(data):
 results.append(data)
 (run/'target-results.json').write_text(json.dumps(results,indent=2)+'\n')

def compile_one(module,stage):
 src=root/(module.replace('.','/')+'.lean')
 out=build/(module.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 assert not out.exists() and not out.is_symlink(),out
 log=run/(stage+'-'+module+'.log')
 cmd=['lean','-s',str(lean_stack_kib),'-o',str(out),str(src.relative_to(root))]
 t=time.monotonic()
 with log.open('w') as f:p=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT)
 data={'module':module,'stage':stage,'source_sha256':sha(src),'command':cmd,'exit':p.returncode,'elapsed_seconds':round(time.monotonic()-t,3),'log':str(log.relative_to(root))}
 if p.returncode==0:
  if re.search(r"warning: declaration uses 'sorry'",log.read_text()):data['exit']=86;data['gate_failure']='Compiler reported an admitted declaration or anonymous example'
  else:data['output_sha256']=sha(out)
 return data

def compile_dag(modules,stage,jobs=4):
 deps={}
 for m in modules:
  src=root/(m.replace('.','/')+'.lean');text=src.read_text()
  ds=set(re.findall(r'^import\s+([\w.]+)\s*$',text,re.M))
  for d in ds:
   if d.startswith('PlanarHom') and not (root/(d.replace('.','/')+'.lean')).is_file():raise RuntimeError(f'Missing local import {m}: {d}')
  deps[m]=ds & set(modules)
 done={x['module'] for x in results if x['stage']==stage and x['exit']==0};pending=set(modules)-done;active={}
 with cf.ThreadPoolExecutor(max_workers=jobs) as pool:
  while pending or active:
   for m in sorted(pending):
    if len(active)>=jobs:break
    if deps[m]<=done:
     pending.remove(m);active[pool.submit(compile_one,m,stage)]=m
   if not active:raise RuntimeError(f'Import cycle: {pending}')
   fs,_=cf.wait(active,return_when=cf.FIRST_COMPLETED)
   for fut in fs:
    m=active.pop(fut);r=fut.result();record(r)
    print(f'{stage}: {len(done)+1}/{len(modules)} {m} exit={r["exit"]}',flush=True)
    if r['exit']:
     print((root/r['log']).read_text(),flush=True)
     # Other already-started compilers only write fresh regular files within this run.
     raise RuntimeError(f'Compilation failed: {m}, exit {r["exit"]}')
    done.add(m)

def audit_regression(suite):
 generated=run/'audit-inputs'/f'{suite}.lean';generated.parent.mkdir(parents=True,exist_ok=True)
 generated.write_text(audit_template.replace('-- PLGH_REGRESSION_IMPORT','import scripts.'+suite))
 out=build/'RegressionAuditOutputs'/f'{suite}.olean';out.parent.mkdir(parents=True,exist_ok=True)
 assert not out.exists() and not out.is_symlink()
 log=run/f'regression-audit-scripts.{suite}.log'
 cmd=['lean','-s',str(lean_stack_kib),'-o',str(out),str(generated.relative_to(root))];t=time.monotonic()
 with log.open('w') as f:p=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT)
 result={'module':'scripts.'+suite,'stage':'isolated-regression-audit','source_path':str(generated.relative_to(root)),'source_sha256':sha(generated),'command':cmd,'exit':p.returncode,'elapsed_seconds':round(time.monotonic()-t,3),'log':str(log.relative_to(root))}
 text=log.read_text()
 if p.returncode==0:
  if re.search(r"warning: declaration uses 'sorry'",text):result['exit']=86
  else:
   assert 'REGRESSION_AXIOM_AUDIT_PASS:' in text,f'Missing regression audit marker: {suite}'
   expected=set()
   def visit_script(name):
    if name in expected:return
    expected.add(name)
    for dependency in re.findall(r'^import (scripts\.[\w.]+)\s*$',(root/(name.replace('.','/')+'.lean')).read_text(),re.M):visit_script(dependency)
   visit_script('scripts.'+suite)
   assert set(re.findall(r'AUDITED_MODULE ([\w.]+)',text))==expected,f'Regression audit module coverage mismatch: {suite}'
   result['declarations']=[list(x) for x in re.findall(r'^CHECKED_ORIGIN ([\w.]+) (.+)$',text,re.M)]
   assert len({tuple(x) for x in result['declarations']})==int(re.search(r'REGRESSION_DECLARATION_COUNT=(\d+)',text)[1]),f'Regression declaration count mismatch: {suite}'
   assert all(x[0] in expected for x in result['declarations']),f'Unexpected declaration origin: {suite}'
   result['output_sha256']=sha(out)
 return result

try:
 modules=['PlanarHom']+[p.relative_to(root).with_suffix('').as_posix().replace('/','.') for p in sorted((root/'PlanarHom').rglob('*.lean'))]
 # The public aggregate must actually include every accepted production module.
 def closure(m,seen):
  if m in seen:return
  seen.add(m)
  for d in re.findall(r'^import\s+(PlanarHom(?:\.[\w]+)*)\s*$',(root/(m.replace('.','/')+'.lean')).read_text(),re.M):closure(d,seen)
 seen=set();closure('PlanarHom',seen)
 assert seen==set(modules),f'Production modules missing from aggregate: {set(modules)-seen}'
 (run/'project-modules.json').write_text(json.dumps(sorted(modules),indent=2)+'\n')
 if os.environ.get('PLGH_RESUME_FROM'):
  from resume_fresh import restore_failed_fresh
  retained,receipt=restore_failed_fresh(root,os.environ['PLGH_RESUME_FROM'],run,build,snapshot,version,dependency_evidence,modules)
  results.extend(retained)
  (run/'target-results.json').write_text(json.dumps(results,indent=2)+'\n')
  summary.update(retained_fresh_compilations=len(retained),resume_source_run=receipt['source_run'],resume_source_snapshot=receipt['source_snapshot'],resume_source_condition=receipt['source_terminal_condition'],resume_manifest_sha256=sha(run/'resume-manifest.json'),unchanged_mathematical_sources_across_segments=True)
  (run/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
  print(f'Validated continuation: {len(retained)} source-compiled objects from the preserved fresh segment ({receipt["source_terminal_condition"]}); no pre-campaign project cache',flush=True)
 compile_dag(modules,'build',int(os.environ.get('PLGH_JOBS','4')))
 # Compile the independent proposition/proof interface with the same fresh project build.
 audit_modules=[p.relative_to(root).with_suffix('').as_posix().replace('/','.') for p in sorted((root/'Audit').glob('*.lean'))]
 assert set(audit_modules)=={'Audit.Contracts','Audit.Solutions','Audit.Check','Audit.Inventory','Audit.ReviewedStatements','Audit.ReviewedSolutions','Audit.ReviewedCheck'}
 compile_dag(audit_modules,'contract',int(os.environ.get('PLGH_JOBS','4')))
 contract_config=json.loads((root/'Audit/contracts.json').read_text())
 assert set(contract_config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
 contract_log=(run/'contract-Audit.Check.log').read_text()
 expected_contracts={(r['solution'],r['statement']) for r in contract_config['theorem_names']}
 actual_contracts=set(re.findall(r'CONTRACT_PASS ([\w.]+) == ([\w.]+)',contract_log))
 assert expected_contracts==actual_contracts and len(actual_contracts)==3
 negative_controls=set(re.findall(r'EXTRA_PREMISE_REJECTED ([\w.]+)',contract_log))
 assert negative_controls=={s for s,_ in expected_contracts}
 target_config=json.loads((root/'Audit/targets.json').read_text())
 inventory_log=(run/'contract-Audit.Inventory.log').read_text()
 expected_targets={(item,name) for item,names in target_config['items'].items() for name in names}
 actual_targets=set(re.findall(r'PAPER_TARGET ([\w.]+) ([\w.]+)',inventory_log))
 assert expected_targets==actual_targets
 paper_items=set(re.findall(r'PAPER_ITEM_CHECKED ([\w.]+)',inventory_log))
 assert paper_items==set(target_config['items']) and len(paper_items)==58
 assert len(actual_targets)==100
 summary.update(contract_checks=len(actual_contracts),negative_contract_controls=len(negative_controls),
   paper_items_checked=len(paper_items),paper_declarations_checked=len(actual_targets),
   separate_audit_modules=len(audit_modules))
 reviewed_config=json.loads((root/'Audit/reviewed-contracts.json').read_text())
 reviewed_log=(run/'contract-Audit.ReviewedCheck.log').read_text()
 expected_reviewed={(r['item'],r['solution'],r['statement']) for r in reviewed_config['entries']}
 actual_reviewed=set(re.findall(r'REVIEWED_CONTRACT_PASS ([\w.]+) ([\w.]+) == ([\w.]+)',reviewed_log))
 assert actual_reviewed==expected_reviewed and len(actual_reviewed)==100
 assert {r['item'] for r in reviewed_config['entries']}==paper_items
 assert {(r['item'],r['original']) for r in reviewed_config['entries']}==expected_targets
 reviewed_negative=set(re.findall(r'REVIEWED_EXTRA_PREMISE_REJECTED ([\w.]+)',reviewed_log))
 assert reviewed_negative=={r['solution'] for r in reviewed_config['entries']}
 assert set(reviewed_config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
 summary.update(reviewed_signature_contracts=len(actual_reviewed),reviewed_contract_items=len(paper_items),
   reviewed_negative_controls=len(reviewed_negative))
 test_log=run/'archive-safety-tests.log'
 with test_log.open('w') as handle:
  test_result=subprocess.run([sys.executable,'scripts/test_release.py'],env=env,stdout=handle,stderr=subprocess.STDOUT)
 assert test_result.returncode==0,test_log.read_text()
 assert 'Ran 14 tests' in test_log.read_text() and 'OK' in test_log.read_text()
 summary.update(archive_safety_tests=14)
 suites=json.loads((root/'scripts/regression-suites.json').read_text())
 compile_dag(['scripts.'+x for x in suites],'regression',int(os.environ.get('PLGH_JOBS','4')))
 for name in ['AxiomAudit','CompletedStatementScopeAudit',*gates['named_axiom_audits']]:
  r=compile_one('scripts.'+name,'audit');record(r)
  if r['exit']:raise RuntimeError(f'Audit failed: {name}; { (root/r["log"]).read_text() }')
  text=(root/r['log']).read_text()
  if name=='AxiomAudit':
   assert 'AXIOM_AUDIT_PASS:' in text
   assert set(re.findall(r'AUDITED_MODULE ([\w.]+)',text))==set(modules),'Production module-origin audit coverage mismatch'
  if name=='CompletedStatementScopeAudit':assert text.count('SCOPE_PASS ')==7
  if name in gates['named_axiom_audits']:
   groups=re.findall(r'depends on axioms: \[([^]]*)\]',text,re.S)
   report_count=len(groups)+len(re.findall(r'does not depend on any axioms',text))
   assert report_count==gates['named_axiom_audits'][name],f'Named audit declaration coverage mismatch: {name}'
   for g in groups:assert {x.strip() for x in g.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}
  if name in gates.get('script_origin_audit_markers',{}):
   assert gates['script_origin_audit_markers'][name] in text,f'Missing origin audit marker: {name}'
   assert set(re.findall(r'AUDITED_MODULE ([\w.]+)',text))==set(modules),f'Incomplete module-origin audit: {name}'
  print('audit:',name,'PASS',flush=True)
 regression_audits=[]
 with cf.ThreadPoolExecutor(max_workers=int(os.environ.get('PLGH_JOBS','4'))) as pool:
  pending={pool.submit(audit_regression,suite):suite for suite in suites}
  for future in cf.as_completed(pending):
   result=future.result();record(result);regression_audits.append(result)
   if result['exit']:raise RuntimeError(f'Isolated regression audit failed: {result["module"]}; {(root/result["log"]).read_text()}')
   print(f'isolated regression audit: {len(regression_audits)}/{len(suites)} {result["module"]} PASS',flush=True)
 assert {x['module'] for x in regression_audits}=={'scripts.'+x for x in suites},'A regression suite was not audited'
 regression_declarations={tuple(x) for result in regression_audits for x in result['declarations']}
 (run/'regression-audit-results.json').write_text(json.dumps({'suites':sorted(x['module'] for x in regression_audits),'distinct_declarations_by_origin':len(regression_declarations),'declarations':sorted(regression_declarations)},indent=2)+'\n')
 # Two recovered spectral full-project audits must have actually run in this fresh build.
 for module,expected in gates.get('execution_output_checks',{}).items():
  lines=(run/('build-'+module+'.log')).read_text().splitlines()
  assert [x for x in lines if x.startswith('mkRat ')]==expected['mkRat_lines'],(module,'rational execution mismatch')
  assert [x for x in lines if x in ('true','false')]==expected['boolean_lines'],(module,'Boolean execution mismatch')
  if 'list_lines' in expected:assert [x for x in lines if x.startswith('[')]==expected['list_lines'],(module,'list execution mismatch')
  if 'exact_lines' in expected:assert lines==expected['exact_lines'],(module,'exact execution mismatch')
 for module,marker in gates['embedded_audit_markers'].items():
  assert marker in (run/('build-'+module+'.log')).read_text()
 for module in gates['aggregate_regression_modules']:assert module in modules,f'Missing aggregate regression module {module}'
 assert subprocess.check_output([sys.executable,'scripts/snapshot.py'],text=True)==snapshot,'Source changed during verification'
 for p,digest in protected.items():assert sha(Path(p))==digest,f'External evidence changed: {p}'
 for pin in dependency_evidence:
  directory=dependency_root/pin['name']
  assert subprocess.check_output(['git','--no-optional-locks','-C',str(directory),'rev-parse','HEAD'],text=True).strip()==pin['expected_revision']
  assert not subprocess.check_output(['git','--no-optional-locks','-C',str(directory),'status','--porcelain','--untracked-files=no'],text=True)
 (run/'source-guards.log').write_text(f'PASS: verified tree snapshot unchanged; {len(protected)} external evidence inputs unchanged.\n')
 audit=(run/'audit-scripts.AxiomAudit.log').read_text()
 summary.update(status='PASS',exit=0,project_modules=len(modules)-1,script_regression_suites=len(suites),aggregate_added_regression_modules=len(gates['aggregate_regression_modules']),named_axiom_audits_passed=list(gates['named_axiom_audits']),embedded_audit_markers_passed=list(gates['embedded_audit_markers']),project_declarations=int(re.search(r'PROJECT_DECLARATION_COUNT=(\d+)',audit)[1]),project_theorem_declarations=int(re.search(r'PROJECT_THEOREM_COUNT=(\d+)',audit)[1]),regression_declarations=len(regression_declarations),isolated_regression_audits=len(regression_audits),project_and_regression_declarations=int(re.search(r'PROJECT_DECLARATION_COUNT=(\d+)',audit)[1])+len(regression_declarations),external_evidence_unchanged=len(protected),full_project_audit_selection='declaration module origin; includes any namespace and private/generated helpers',allowed_axioms=['propext','Classical.choice','Quot.sound'])
except Exception as e:
 summary.update(status='FAILED',exit=1,error=str(e));traceback.print_exc()
finally:
 summary['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 summary['elapsed_seconds']=round(time.monotonic()-start,3)
 summary['targets_completed']=len(results)
 (run/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 (run/'verify.exit').write_text(str(summary.get('exit',1))+'\n')
 print(json.dumps(summary,indent=2),flush=True)
 if summary['status']=='PASS':
  (root/'logs/latest-success.json').write_text(json.dumps({'run':str(run.relative_to(root)),**summary},indent=2)+'\n')
sys.exit(summary.get('exit',1))
