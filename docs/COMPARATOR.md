# Statement checks

## Review interfaces

| Purpose | Statements | Solutions | Checker |
| --- | --- | --- | --- |
| Theorems 1.1, 1.3 and the rectangular case of Corollary 12.2 | [Contracts](../Audit/Contracts.lean) | [Solutions](../Audit/Solutions.lean) | [Check](../Audit/Check.lean) |
| 100 statements and interfaces covering all 58 numbered paper results | [ReviewedStatements](../Audit/ReviewedStatements.lean) | [ReviewedSolutions](../Audit/ReviewedSolutions.lean) | [ReviewedCheck](../Audit/ReviewedCheck.lean) |

The three principal propositions are written out explicitly in `Contracts.lean`.
The additional interfaces were initially extracted from elaborated library types
and checked against the [paper correspondence and model review](PAPER_AUDIT.md).
Both sets are committed source files; verification never regenerates them from
the solutions. The solution modules do not import the statement modules.

Review the definitions imported by these files together with the hypotheses and
conclusions. Type agreement detects changes to the formal specification;
correspondence with the paper is established by mathematical review of that
specification, rather than by type comparison alone.

## Verification method

The project checkers:

- Compare complete types, aligning universe parameters where necessary.
- Check transitive axiom dependencies against `propext`, `Classical.choice`, and
  `Quot.sound`.
- Test that adding an extra premise to each solution type is rejected.
- Require the complete inventory of 58 paper items and 100 additional interfaces.

Algorithm and reduction interfaces include their machine, correctness, cost,
and query-validity fields. The full verifier also compiles the proof library and
audits every project declaration by its originating module.

These checks run in the compiled Lean environment and rely on the committed
statement definitions and their imports. Those imports include mathematical
definitions and may include proofs. The configurations under `Audit/` are inputs
to the project checkers.

## Relationship to Lean Comparator

The official [Lean Comparator](https://github.com/leanprover/comparator) compares
separately exported challenge and solution environments and replays the exported
proofs through Lean's kernel. Its sandboxed workflow also isolates the build and
export processes.

This repository uses the project checkers described above. The official
Comparator has not been run on this development. The checks provide neither
process sandboxing nor proof replay in a separately reconstructed environment,
and no external kernel implementation has been used. Proofs are checked by the
pinned Lean 4.24.0 kernel during compilation.

For the distinctions between compilation, axiom inspection, statement comparison,
and kernel replay, see the
[Lean proof-validation reference](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).
