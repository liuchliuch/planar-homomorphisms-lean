# Mathematical and computational semantics

## Inputs and partition functions

`PlanarHom/Basic.lean` defines a finite sum over all vertex colorings, with one
vertex-weight factor per vertex and one matrix factor per edge occurrence.
A loop uses its diagonal entry; repeated edges remain distinct. The empty graph
has value one, and isolated vertices contribute their full weight sum.

`GraphCode` and `MixedCode` encode explicit occurrence lists. Vertex count is
unary, so exponentially many isolated vertices cannot be hidden in a short
binary header. Vertex indices and arithmetic values use binary encodings.
Successful noncanonical input encodings are normalized by proved machines.

`MultiGraph.Planar` means existence of an ordinary crossing-free continuous
plane drawing. An embedding is not part of the main input. The finite drawing
to polygonal/ribbon bridge is proved in `PlanarRibbonExistence.lean`; the
computed LR rotation and Fisher/FKT pipeline use the original planar promise.

## FP and #P hardness

`Complexity.FP` is existence of a mathlib finite-control TM2 program with
polynomial time in the supplied binary encodings. Composition is supplied by a
proved compiler. `PromisePolyTimeTuringReduction` contains a fixed finite oracle
machine and polynomial bound, works for every extension of the promised source
oracle, and queries only valid source inputs. A query charges its entire query
and answer word, as well as the transition.

`SharpP` counts accepting paths of independently defined finite nondeterministic
machines, with every branch polynomially bounded. Bridges to certificate counting
and conventional single-tape machines are proved. Final Potts and biased-Boolean
hardness foundations are proved reductions, not axioms or unfilled fields.

A fixed language, field presentation, color order, and target matrix are
nonuniform constants. These theorems do not provide a single uniform algorithm
that decides the classification of arbitrary input matrices. Existence of a
machine in an FP theorem is not a claim that the repository is a practical
partition-function executable.

The easy and hard branches are implications from structural membership and its
negation. They do not assume a separation of FP and #P, or establish that FP
membership itself is equivalent to the displayed structural predicate.

## Numerical twins and weighted classifications

`Structures.PositiveVertexWeightClass` uses equality of full numerical rows and
the sum of the original weights in each equivalence class. Support twins alone
are insufficient. Weighted Ising coordinates are nondegenerate (`rho != 1`),
and class weights are constant only in those coordinates. For nonnegative
vertex weights, zero-weight colors are deleted before the quotient. Empty
surviving domains are handled separately.

## Appendix A

The field is presented as a finite extension of a fixed rational-function field,
with a fixed finite basis and an embedding into the reals where order is used.
Coordinates are exact dense polynomial/rational-function data; representatives
need not be unique. The model does not postulate real arithmetic, a sign oracle,
a canonical representative, or an output-field conversion oracle.

`RepresentedBit.Problem.InFP` requires an ordinary program producing a valid
answer. `RepresentedBit.Reduction` works for every valid representative returned
by the source. Its work bound is polynomial in input length plus actual reply
volume; query count and each query length have independent input-polynomial
bounds. It would be incorrect to promise input-only time for arbitrarily padded
oracle replies.

Lemma A.1 proves arithmetic, nonsingular linear-system solving, fixed products,
finite-extension arithmetic, prescribed-subfield descent, and ordinary integer
conversion. Its partition-output bound is a size result, not an evaluation
algorithm. The corresponding algorithm/closure constructions are used by the
appendix hardness and tractability endpoints.

## Supplied surface embeddings

Corollary 12.8 takes a finite graph, cyclic rotation rows, and complement-region
genera/boundary attachments. Finite validity checks connected incidence and the
Euler relation for the fixed orientable ambient genus. Homology coordinates,
Pfaffian signs, and orientation solvers are computed internally.

This finite combinatorial encoding is the formal boundary of the surface
theorem. This audit has not established an equivalence with a separate general
topological-manifold library. The original paper expressly supplies an embedding;
this is distinct from the main theorems' ordinary planar input.
