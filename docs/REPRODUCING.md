# Reproducing the verification and release

## Pinned inputs

- Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
- mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` and eight further revisions in
  `lake-manifest.json`.
- Python 3.11+, Bash, Git, and Elan or the pinned Lean binaries on `PATH`.
- The paper checksum in `paper/SHA256SUMS`.

Dependencies are not bundled. Do not regenerate the lockfile to build.
`SOURCE_PROVENANCE.json` pins the exact accepted source, verifier, and configuration
inventory; `RELEASE_MANIFEST.json` and its checksum cover every distributed file.
These are integrity records, not digital signatures.

## Full verification

```sh
lake exe cache get
PLGH_JOBS=4 PYTHONDONTWRITEBYTECODE=1 bash scripts/verify.sh reproduction-1
```

Choose a new label for each run. The verifier creates fresh project objects under
`logs/runs/`; it reuses only pinned third-party objects. It verifies dependency
revisions and rejects modified tracked dependency sources and project artifacts
inside dependency caches. `PLGH_DEPENDENCY_ROOT` can select an existing dependency
directory explicitly; otherwise `.lake/packages` is used.

The required gates are:

- All 4,125 production modules, the aggregate, seven audit modules, and 81
  regression suites compile from source.
- A module-origin audit covers every project declaration, including private and
  generated declarations. All regression suites receive isolated origin audits.
- Three independently written contracts and 100 fixed reviewed interface types
  pass full-type comparison, transitive axiom checks, and added-premise rejection.
  The inventory covers 58 paper items and 100 entry declarations.
- Named statement audits, integration-output gates, source immutability guards,
  and 14 archive/environment/evidence regression tests pass.

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Source checks also
reject `axiom`, `sorry`, `admit`, and `sorryAx` outside comments and strings in
the proof library. The separate official challenge permits specification
placeholders; the isolated negative axiom control permits its deliberately
untrusted axiom. Neither can be imported by proof modules.
Each Lean process uses one worker and a 64 MiB thread stack. Four concurrent
processes are the default; lower `PLGH_JOBS` on memory-constrained machines.
Actual commands, exits, timings, and complete raw logs are retained locally in
the run directory. The verifier makes no promise about its own runtime.

## Official Comparator

```sh
python3 scripts/compare.py --jobs 2
```

This Linux command checks the 103 fixed interfaces, the permitted axioms, fresh
Lean kernel replay, and two negative controls. It requires the pinned Landrun and
a user systemd session. On macOS, add `--local` to run explicitly without process
isolation. The official challenge and negative controls are separate Lake targets
and are excluded from the default proof build. See [COMPARATOR.md](COMPARATOR.md)
for installation, tool pins and scope.

## Build a source archive

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/release.py stage
PYTHONDONTWRITEBYTECODE=1 python3 scripts/release.py rebuild .tmp/candidate-SNAPSHOT.tar.gz --jobs 4
PYTHONDONTWRITEBYTECODE=1 python3 scripts/release.py publish .audit/archive-ARCHIVEHASH/receipt.json
```

Replace the example paths with those printed by the preceding command. `publish`
creates a local archive; it does not upload anything. The candidate is unverified
until the extracted source passes the full verifier. Existing evidence is moved
to `.audit/previous-evidence-*` before the new successful run is exported.

The final archive preserves the exact source/tool/configuration snapshot of the
successful extracted build. Publication adds its verification evidence and report,
then safely extracts the final archive and compares every distributed file.
The source snapshot, including verifier changes, must match before publication.

Portable evidence retains per-target commands and source/object hashes, contract
checks, whole-project origin checks, and source guards. Large retained logs use
gzip. The log index records uncompressed hashes and sizes, including omitted
reproducible diagnostics, generated audit copies, and empty files. Older runs,
compiled objects, dependency caches, machine toolchains, Finder metadata, and
historical cleanup reports are excluded.

```sh
python3 scripts/release.py inspect planar-homomorphisms-reviewed-SNAPSHOT.tar.gz
shasum -a 256 -c planar-homomorphisms-reviewed-SNAPSHOT.tar.gz.sha256
```

Archive validation rejects duplicate names, unsafe paths, links, special files,
unexpected modes, unlisted members, and content mismatches before extraction.
