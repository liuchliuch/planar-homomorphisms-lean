"""Continue a failed or explicitly interrupted fresh campaign, retaining its evidence chain."""
from pathlib import Path
import hashlib, json, re, shutil


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def regular(root, path):
    path = Path(path)
    assert path.is_absolute() and path.is_relative_to(root), path
    for p in [path, *path.parents]:
        if p == root:
            break
        assert not p.is_symlink(), ('Nonregular resume input', p)
    assert path.is_file(), path
    return path


def snapshot_rows(text):
    rows = {}
    for line in text.splitlines():
        h, rel = line.split(None, 1)
        assert re.fullmatch('[0-9a-f]{64}', h) and rel not in rows
        rows[rel] = h
    return rows


def restore_failed_fresh(root, relative, run, build, snapshot, version, pins, modules):
    rel = Path(relative)
    assert not rel.is_absolute() and '..' not in rel.parts
    assert rel.parts[:2] == ('logs', 'runs') and len(rel.parts) == 3
    old = root / rel
    assert old != run
    read = lambda name: regular(root, old / name)
    state = json.loads(read('summary.json').read_text())
    assert state['status'] in {'FAILED', 'RUNNING'}
    assert state['source_only_project_recompile'] is True
    assert state['baseline_project_artifacts_reused'] is False
    interrupted = None
    if state['status'] == 'FAILED':
        assert state['exit'] != 0
        assert read('verify.exit').read_text().strip() == str(state['exit'])
    else:
        # Never rewrite a stale RUNNING receipt as a reported compiler failure.
        assert not (old / 'verify.exit').exists()
        interrupted = json.loads(read('interruption.json').read_text())
        assert interrupted['status'] == 'INTERRUPTED'
        assert interrupted['source_run'] == str(rel)
        assert interrupted['source_snapshot'] == state['snapshot']
        assert interrupted['summary_sha256'] == digest(read('summary.json'))
        assert interrupted['results_sha256'] == digest(read('target-results.json'))
        assert interrupted['executor_session_probe'] == 'UNKNOWN_PROCESS_ID'
        assert interrupted['compiler_exit_observed'] is False
    previous_text = read('source-snapshot.sha256').read_text()
    assert hashlib.sha256(previous_text.encode()).hexdigest() == state['snapshot']
    before, after = snapshot_rows(previous_text), snapshot_rows(snapshot)
    changed = {p for p in before.keys() | after.keys() if before.get(p) != after.get(p)}
    # Only the explicit verification-resource/continuation fix may differ.
    allowed = {'scripts/verify_current.py', 'scripts/resume_fresh.py',
               'SOURCE_PROVENANCE.json'}
    assert changed <= allowed, ('Proof, regression, dependency or unrelated tool changed', changed - allowed)
    assert read('toolchain.txt').read_text() == version
    old_pins = json.loads(read('dependency-pins.json').read_text())
    assert {(p['name'], p['expected_revision'], p['actual_revision'], p['tracked_source_clean']) for p in old_pins} == {
        (p['name'], p['expected_revision'], p['actual_revision'], p['tracked_source_clean']) for p in pins}
    assert set(json.loads(read('project-modules.json').read_text())) == set(modules)
    entries = json.loads(read('target-results.json').read_text())
    selected = [x for x in entries if x['stage'] == 'build' and x['exit'] == 0]
    if interrupted is not None:
        assert interrupted['completed_results'] == len(entries)
    previous_resume = None
    if state.get('retained_fresh_compilations', 0):
        prior_file = read('resume-manifest.json')
        assert digest(prior_file) == state['resume_manifest_sha256']
        previous_resume = json.loads(prior_file.read_text())
        assert previous_resume['retained_fresh_compilations'] == state['retained_fresh_compilations']
        assert previous_resume['pre_campaign_project_cache_reused'] is False
        indexed = {x['module']:x for x in selected}
        for item in previous_resume['records']:
            old_item = indexed[item['module']]
            assert old_item['source_sha256'] == item['source_sha256']
            assert old_item['output_sha256'] == item['object_sha256']
    assert len({x['module'] for x in selected}) == len(selected)
    checked = []
    for item in selected:
        m = item['module']
        assert m in modules
        source = regular(root, root / (m.replace('.', '/') + '.lean'))
        obj = read('build/' + m.replace('.', '/') + '.olean')
        log = regular(root, root / item['log'])
        assert log.parent == old
        assert item['source_sha256'] == digest(source) == before[str(source.relative_to(root))]
        assert item['output_sha256'] == digest(obj)
        assert "warning: declaration uses 'sorry'" not in log.read_text()
        checked.append((item, obj, log))
    names = {x[0]['module'] for x in checked}
    for item, _, _ in checked:
        imports = set(re.findall(r'^import\s+(PlanarHom(?:\.\w+)*)\s*$',
                      (root / (item['module'].replace('.', '/') + '.lean')).read_text(), re.M))
        assert imports <= names, ('Incomplete retained dependency closure', item['module'], imports - names)
    # No mutation occurs before all resume source, object and closure checks pass.
    evidence = run / 'resume-evidence'
    evidence.mkdir()
    copied = []
    for name in ('summary.json', 'source-snapshot.sha256', 'target-results.json',
                 'toolchain.txt', 'dependency-pins.json',
                 'accepted-source-guard.log', 'project-modules.json'):
        shutil.copy2(read(name), evidence / name)
    for name in ('verify.exit', 'interruption.json', 'resume-manifest.json'):
        if (old / name).exists():
            shutil.copy2(read(name), evidence / name)
    if previous_resume is not None:
        previous_evidence = old / 'resume-evidence'
        assert previous_evidence.is_dir() and not previous_evidence.is_symlink()
        for source in previous_evidence.rglob('*'):
            assert not source.is_symlink()
            if source.is_file():
                regular(root, source)
                target = evidence / 'resume-evidence' / source.relative_to(previous_evidence)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, target)
    for item in entries:
        if item['exit'] != 0:
            log = regular(root, root / item['log'])
            assert log.parent == old
            shutil.copy2(log, evidence / log.name)
    for item, obj, log in checked:
        target = build / (item['module'].replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        assert not target.exists() and not target.is_symlink()
        shutil.copyfile(obj, target)
        assert digest(target) == item['output_sha256']
        copied_log = run / log.name
        shutil.copy2(log, copied_log)
        record = dict(item)
        record.setdefault('compiled_in_fresh_segment', str(rel))
        record.update(log=str(copied_log.relative_to(root)),
                      retained_via_fresh_segment=str(rel),
                      copied_from_fresh_object=str(obj.relative_to(root)))
        copied.append(record)
    receipt = {'source_run':str(rel),'source_snapshot':state['snapshot'],
       'source_summary_sha256':digest(read('summary.json')),
       'source_results_sha256':digest(read('target-results.json')),
       'source_terminal_condition':'INTERRUPTED' if interrupted is not None else 'FAILED',
       'source_interruption_sha256':digest(read('interruption.json')) if interrupted is not None else None,
       'recursive_predecessor_evidence_preserved':previous_resume is not None,
       'prior_resume_manifest_sha256':digest(read('resume-manifest.json')) if previous_resume is not None else None,
       'unchanged_proof_and_regression_sources':True,
       'changed_verification_files':sorted(changed),
       'retained_fresh_compilations':len(copied),
       'pre_campaign_project_cache_reused':False,
       'failed_run_unchanged':True,
       'records':[{'module':x['module'],'source_sha256':x['source_sha256'],
                   'object_sha256':x['output_sha256']} for x in copied]}
    (run / 'resume-manifest.json').write_text(json.dumps(receipt, indent=2)+'\n')
    return copied, receipt
