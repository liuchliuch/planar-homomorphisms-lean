# Verification results

The final source, audit interface, and verifier were freshly compiled from an extracted candidate source archive. The delivered archive adds these evidence files and this report; its complete source/tool/configuration snapshot is identical to that fresh build. A final safe extraction checks all delivered files against the source tree.

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
- Official Linux comparator: not run; no equivalent sandbox claim

See `verification/final/` for per-target commands, exit codes, source/object hashes, statement checks, origin audits, and unchanged-source guards. Large retained logs are gzip-compressed; `log-index.json` records the uncompressed size and hash of every run file and identifies omitted reproducible diagnostics and generated audit inputs. Full raw logs are produced locally under `logs/runs/` when the verifier runs. `verification/archive-rebuild.json` records the actual extraction, command, timings, and dependency location. Absolute execution paths are historical evidence, not required build inputs.

This kernel/dependency result is separate from the statement and model review in [PAPER_AUDIT.md](PAPER_AUDIT.md). It is not an independent kernel implementation or a manual review of every proof line.

The verification results above identify the prepared source snapshot. Subsequent
README and verification-method documentation edits, and the addition of a GitHub
Actions workflow, leave that source/tool/configuration snapshot unchanged.
The current file inventory and publication changes are recorded in
[RELEASE_MANIFEST.json](../RELEASE_MANIFEST.json).
