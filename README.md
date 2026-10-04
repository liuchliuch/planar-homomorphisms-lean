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

## Statement verification

The official [Lean Comparator](https://github.com/leanprover/comparator) checks
[Challenge.lean](Audit/Official/Challenge.lean) against
[Solution.lean](Audit/Official/Solution.lean). The challenge fixes the three main
propositions and 100 additional interfaces covering all 58 numbered paper results.
The solution supplies proofs and implementations at those same types.

Comparator compares the exported declarations and their dependencies, checks the
permitted axioms, and rechecks the solution in a fresh Lean kernel environment.
Linux CI isolates compilation and export with Landrun. The checking tools and
all mathematical dependencies are pinned.

On Linux, with the pinned Landrun installed and a running user systemd session:

```sh
python3 scripts/compare.py --jobs 2
```

For development on macOS, use `--local`; this explicitly disables process
isolation. Both modes also check that a solution with an extra premise and a
solution using an extra axiom are rejected. See
[Comparator setup and scope](docs/COMPARATOR.md) and
[verification results](docs/VERIFICATION.md).

## Citation and license

Use [CITATION.cff](CITATION.cff) to cite the accompanying paper.
No software license has been specified for this source release.
