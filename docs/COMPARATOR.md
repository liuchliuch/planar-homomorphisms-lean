# Statement/proof separation and comparator scope

## Local checks included in this release

| Purpose | Statements | Solutions | Checker |
| --- | --- | --- | --- |
| Three independently written propositions: Theorems 1.1, 1.3 and the rectangular clause of Corollary 12.2 | [Contracts](../Audit/Contracts.lean) | [Solutions](../Audit/Solutions.lean) | [Check](../Audit/Check.lean) |
| 100 fixed full types across all 58 paper items | [ReviewedStatements](../Audit/ReviewedStatements.lean) | [ReviewedSolutions](../Audit/ReviewedSolutions.lean) | [ReviewedCheck](../Audit/ReviewedCheck.lean) |

Statements are definitions with no proof placeholders. The solution files do not
import the statement files. The checkers compare full types, align universe
parameters where needed, reject an added-premise negative control for each entry,
and permit only `propext`, `Classical.choice`, and `Quot.sound` in the transitive
axiom dependencies. The full verifier also requires the exact 58-item inventory
and audits all project declarations by their source-module origin.

The 100 reviewed signatures were derived from elaborated source interfaces and
checked against the [paper/model review](PAPER_AUDIT.md). They are fixed source
text and are never regenerated from solution types during verification. They
protect against subsequent statement drift; they cannot independently establish
that the initial formal interpretation matches the paper. The three primary
contracts were written independently.

Data-valued endpoints retain their complete reduction types, including machines,
correctness, cost, and query-validity fields. Their checks are not merely checks
that names exist. The configurations under `Audit/` belong to these local
checkers; they are not official comparator configuration files.

## Trust boundary

These are in-process checks of trusted source. The statement definitions and
their transitive model imports are part of the trusted review surface; these
imports may themselves contain proofs. The checks do not compare separately
exported environments, isolate hostile metaprograms, or replay proofs through an
independent kernel. Compilation and axiom auditing do not replace mathematical
review of the definitions and hypotheses.

## Official comparator

The [standalone comparator](https://github.com/leanprover/comparator) compares
trusted challenge and solution statements and their dependencies, checks axioms,
and replays the exported solution. Its documented workflow requires a compatible
`lean4export` and a Linux sandbox using `landrun`. The
[newer Lake integration](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator)
uses `bubblewrap` on Linux and the matching toolchain's exporter. These upstream
instructions were checked on 2026-10-04.

This project is pinned to Lean 4.24.0. Its Lake sources do not implement
`lake comparator`; generic help with a zero exit status is not evidence that the
command exists. No compatible official tool/exporter pairing has been validated
for this release, and no official Linux comparator run or independent kernel
replay is claimed. A future integration must validate that compatibility and run
the actual sandbox/export/replay workflow while protecting the trusted statement
sources and their imports.
