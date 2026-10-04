#!/usr/bin/env python3
"""Check the exact portable source/tool/configuration inventory against provenance.
Documentation and evidence are covered by RELEASE_MANIFEST, not this source gate.
"""
from pathlib import Path
import hashlib,json
if not __debug__:
    raise SystemExit('Assertions must be enabled')
root=Path(__file__).resolve().parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prov=json.loads((root/'SOURCE_PROVENANCE.json').read_text())
accepted={}
for record in prov['records']:
    path=Path(record['path'])
    if (path.suffix in {'.lean','.py','.sh','.toml'} and path.parts[0] not in {'docs','paper'}) or str(path) in {'lean-toolchain','lake-manifest.json'}:
        assert str(path) not in accepted, f'Duplicate accepted source record: {path}'
        accepted[str(path)]=record['sha256']
for record in prov['new_verification_support']:
    assert record['path'] not in accepted, f'Duplicate verification support: {record["path"]}'
    accepted[record['path']]=record['sha256']
actual={str(p.relative_to(root)) for p in (root/'PlanarHom').rglob('*.lean')}|{'PlanarHom.lean','lakefile.toml','lean-toolchain','lake-manifest.json'}
actual.update(str(p.relative_to(root)) for p in (root/'scripts').rglob('*') if p.is_file() and p.suffix in {'.lean','.py','.sh','.json'})
actual.update(str(p.relative_to(root)) for p in (root/'Audit').rglob('*') if p.is_file() and p.suffix in {'.lean','.json'})
assert set(accepted)==actual, f'Accepted source inventory mismatch: {set(accepted)^actual}'
for rel,digest in accepted.items():
    assert sha(root/rel)==digest, f'Accepted source hash mismatch: {rel}'
print(f'PASS: {len(accepted)} portable source/tool/configuration records match exact hashes')
