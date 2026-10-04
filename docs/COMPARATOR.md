# Lean Comparator

The repository uses the official [Lean Comparator](https://github.com/leanprover/comparator)
with Lean 4.24.0. Its revision, exporter, kernel replay library, and Linux sandbox
are fixed in [toolchain.json](../Audit/Official/toolchain.json).

## Challenge and solution

| Targets | Fixed specification | Proofs and implementations |
| --- | --- | --- |
| Theorems 1.1, 1.3 and the rectangular case of Corollary 12.2 | [Challenge](../Audit/Official/Challenge.lean) | [Solution](../Audit/Official/Solution.lean) |
| 100 additional interfaces covering 58 numbered paper results | Same challenge file | Same solution file |

The three principal propositions have their hypotheses and conclusions written
out explicitly. The additional interfaces retain the complete types in
[ReviewedStatements.lean](../Audit/ReviewedStatements.lean), checked against the
[paper correspondence and model review](PAPER_AUDIT.md). They are committed
specifications; the verification command never extracts new statements from the
solution.

Challenge and solution use the same declaration names in separate exported
environments. The solution imports only the proof modules, never the challenge
or statement modules. Challenge placeholders specify goals; they are excluded
from the proof library. The three main targets are theorem holes. The 100 other
targets use Comparator's typed definition holes to accommodate both propositions
and data-valued algorithm or reduction interfaces. These holes specify inhabitants
of fixed complete types; the underlying mathematical definitions remain fixed.
The [target inventory](../Audit/Official/targets.json) records every correspondence.

## Run the check

Install Elan, Python 3.11+, Bash and Git. On Linux, also install Go 1.24 and the
pinned Landrun:

```sh
go install github.com/zouuup/landrun/cmd/landrun@811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
lake exe cache get
python3 scripts/compare.py --jobs 2
```

Lake uses the same 64 MiB Lean worker stack as the full source verifier.

The default mode requires Linux and a running user systemd session. It uses
Landrun for the official build and export steps and systemd to restrict Unix
sockets. GitHub Actions supplies this environment. Tools are built outside the
project's writable `.lake` directory, under `~/.cache` by default; `COMPARATOR_HOME`
can select an existing checkout at the pinned revision.

For development on macOS, run:

```sh
python3 scripts/compare.py --local --jobs 4
```

Local mode runs the same official declaration comparison, axiom inspection, and
Lean kernel replay, with process isolation explicitly disabled. The report records
which mode ran. Successful runs write `verification/comparator.json`; complete
logs remain under `.lake/comparator-results/`.

## Required results

The command requires:

- Agreement of all 103 target types, names and universe parameters, and agreement
  of their relevant mathematical dependencies.
- Transitive axiom dependencies contained in `propext`, `Classical.choice`, and
  `Quot.sound`.
- Successful reconstruction of the exported solution in a fresh Lean kernel
  environment.
- Rejection of [an additional premise](../Audit/Official/NegativePremise.lean)
  and [an unpermitted axiom](../Audit/Official/NegativeAxiom.lean), each for the
  expected reason.
- Unchanged verification inputs, tool revisions and checking executables.

The [full verifier](REPRODUCING.md) additionally audits every project declaration
and runs the regression suites. Its existing local statement checkers remain
available for that purpose.

## Scope

Comparator checks agreement with the formal specification. Mathematical review
of the specification and its imported definitions establishes correspondence
with the paper. The additional interfaces originated in elaborated library types;
they are not 100 independent translations of the paper.

Kernel replay uses the pinned Lean kernel in a fresh environment. No second
kernel implementation is enabled. See the
[Lean proof-validation reference](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
for the distinction between compilation, axiom inspection, environment comparison
and kernel replay.
