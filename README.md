# Planar graph homomorphisms in Lean

Lean 4 formalization accompanying Chenghua Liu and Boning Meng,
[*A Dichotomy for Planar Graph Homomorphisms with Nonnegative Weights*](https://liuchliuch.github.io/files/dichotomy-planar-graph-homomorphisms-nonnegative-weights.pdf).
The included [paper](paper/paper.pdf) is pinned by [SHA-256](paper/SHA256SUMS).

## Main results

| Paper result | Formal theorem | Statement for review |
| --- | --- | --- |
| Theorem 1.1: nonnegative interactions | [theorem11](PlanarHom/MainDichotomiesClosed.lean#L13) | [Statement](Audit/Contracts.lean) |
| Theorem 1.3: fixed positive vertex weights | [theorem13](PlanarHom/MainDichotomiesClosed.lean#L15) | [Statement](Audit/Contracts.lean) |
| All 58 numbered proof statements | [Paper-to-Lean map](docs/PAPER_AUDIT.md) | [Statement interfaces](Audit/ReviewedStatements.lean) |

The definitions of the tractable matrix classes are in
[Structures.lean](PlanarHom/Structures.lean). The main results use exact algebraic
bit encodings and ordinary planar multigraphs, including loops, parallel edges,
isolated vertices, and the empty graph. Appendix A uses prescribed representations
in fixed finitely generated real fields; Corollary 12.8 takes a supplied surface
embedding. See [mathematical and computational semantics](docs/SEMANTICS.md).

## Build and verify

Install [Elan](https://github.com/leanprover/elan), Python 3.11+, Bash, and Git.
Lean 4.24.0 and all nine dependency revisions are pinned. From this directory:

```sh
lake exe cache get
PLGH_JOBS=4 PYTHONDONTWRITEBYTECODE=1 bash scripts/verify.sh local-review-1
```

Use a new run label each time. This compiles all 4,125 production modules and
the aggregate from source, compiles all 81 regression suites, audits every
project declaration by module origin, and runs the statement checks. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted axioms.

See [reproduction and packaging](docs/REPRODUCING.md) for the exact commands and
[verification results](docs/VERIFICATION.md) for the delivered source snapshot.
Generated coloring and routing tables are necessary proof inputs.

## Statements and proofs

[Contracts.lean](Audit/Contracts.lean) states Theorems 1.1 and 1.3 and the
rectangular case of Corollary 12.2, with their hypotheses written out explicitly.
[Solutions.lean](Audit/Solutions.lean) supplies the corresponding proofs.

[ReviewedStatements.lean](Audit/ReviewedStatements.lean) records a further
100 formal statements and interfaces covering all 58 numbered paper results;
[ReviewedSolutions.lean](Audit/ReviewedSolutions.lean) connects them to the library.
These statement files are fixed inputs to verification.

The verification command uses the project's Lean-based checkers to compare the
statement and proof types and audit their axiom dependencies. See
[statement checks](docs/COMPARATOR.md) for the checking method and its relationship
to the official Lean Comparator.

## Citation and license

Use [CITATION.cff](CITATION.cff) to cite the accompanying paper.
No software license has been specified for this source release.
