# Verification results

## Prepared proof library

The prepared release was freshly compiled from an extracted source archive.
The evidence below belongs to that original source snapshot. The subsequent
Comparator integration preserves its mathematical library, original audit modules,
and dependency revisions, while adding checking interfaces and tooling.

- Source snapshot: `57a388e0f0b98bbe552ece7d519fa6274b5d0d0543978ac83509fbf877744dd0`
- Lean: `Lean (version 4.24.0, arm64-apple-darwin23.6.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)`
- Full verifier exit: `0`
- Production modules: 4125 plus the aggregate
- Script regressions and isolated audits: 81 each
- Project declarations audited: 278471
- Project theorem declarations: 221161
- Independent proposition contracts: 3
- Reviewed full-type contracts: 100 across 58 paper items
- Numbered paper items inventoried: 58
- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`
- Official Comparator in this original run: not run

See `verification/final/` for per-target commands, exit codes, source/object hashes, statement checks, origin audits, and unchanged-source guards. Large retained logs are gzip-compressed; `log-index.json` records the uncompressed size and hash of every run file and identifies omitted reproducible diagnostics and generated audit inputs. Full raw logs are produced locally under `logs/runs/` when the verifier runs. `verification/archive-rebuild.json` records the actual extraction, command, timings, and dependency location. Absolute execution paths are historical evidence, not required build inputs.

This kernel/dependency result is separate from the statement and model review in [PAPER_AUDIT.md](PAPER_AUDIT.md). It is not an independent kernel implementation or a manual review of every proof line.

## Official Comparator integration

The current source adds the official challenge, solution and two negative
controls under `Audit/Official/`, the pinned runner, and Linux CI. See
[COMPARATOR.md](COMPARATOR.md) for the 103 targets and checking method.

Successful official runs produce [comparator.json](../verification/comparator.json),
which records the exact current source snapshot, tool revisions, platform,
process isolation, type comparison, axiom policy and fresh Lean kernel replay.
The current file inventory is recorded in
[RELEASE_MANIFEST.json](../RELEASE_MANIFEST.json); the prepared proof-library
results above remain historical evidence for their stated snapshot.
