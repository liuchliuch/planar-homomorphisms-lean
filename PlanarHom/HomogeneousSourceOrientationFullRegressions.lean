import PlanarHom.HomogeneousSourceOrientationReduction

noncomputable section
namespace PlanarHom.HomogeneousSourceOrientation.Regressions
open Complexity Complexity.MixedCode

/-- Empty codes issue no connected-component queries. -/
example : prepareComponents ⟨0,[],[]⟩ = ([],[]) := by decide

/-- All three isolated vertices survive, with their original individual side
records restored at the component's local vertex zero. -/
example : prepareComponents ⟨3,[],[(0,0),(1,1),(2,0)]⟩ =
    ([],[⟨1,[],[(0,0)]⟩,⟨1,[],[(0,1)]⟩,⟨1,[],[(0,0)]⟩]) := by decide

/-- Extraction reverses this edge's local vertex order. Canonicalization
correctly moves the intrinsic labels to their actual new vertex indices. -/
example : prepareComponents ⟨3,[(0,1,0)],[(0,0),(1,1),(2,0)]⟩ =
    ([],[⟨2,[(1,0,0)],[(0,1),(1,0)]⟩,⟨1,[],[(0,0)]⟩]) := by decide

/-- Repeated binary occurrences are retained rather than collapsed. -/
example : prepareComponents ⟨2,[(0,1,0),(0,1,0)],[(0,0),(1,1)]⟩ =
    ([],[⟨2,[(1,0,0),(1,0,0)],[(0,1),(1,0)]⟩]) := by decide

/-- The actual root branch follows the reserialized tag, not the old vertex
position or an existential coloring selected in the proof. -/
example : rootSide (canonicalDomains ⟨2,[(1,0,0)],[(1,0),(0,1)]⟩) = true := by decide

/-- Literal domain erasure preserves loops and repeated occurrences as data,
even outside the typed promise. -/
example : eraseDomains ⟨2,[(0,0,0),(0,1,0),(0,1,0)],[(0,0),(1,1)]⟩ =
    ⟨2,[(0,0,0),(0,1,0),(0,1,0)],[]⟩ := rfl

open AlgebraicProductInterpolation TypedBipartiteContext FixedRealRootRestrictions

/-- Exact positive-weight, original-field, original-oracle endpoint. -/
example {x y : ℕ} (L : RealLanguage (x+y) 1 0) (hw : ∀ i,0<L.weights i)
    (hc : Bipartite.Crosses L.matrices (TypedSideSourceAccess.ambientSide x y)) :
    PromisePolyTimeTuringReduction
      (L.typedProblem (domains x y) (fun _ : Fin 1 => crossPolicy) (fun l : Fin 0 => l.elim0))
      L.problem := L.homogeneousSourceOrientation hw hc

/-- Unit background requires no additional computational availability input. -/
example {x y : ℕ} (L : RealLanguage (x+y) 1 0) (hw : ∀ i,L.weights i=1)
    (hc : Bipartite.Crosses L.matrices (TypedSideSourceAccess.ambientSide x y)) :
    PromisePolyTimeTuringReduction
      (L.typedProblem (domains x y) (fun _ : Fin 1 => crossPolicy) (fun l : Fin 0 => l.elim0))
      L.problem := L.homogeneousUnitSourceOrientation hw hc

end PlanarHom.HomogeneousSourceOrientation.Regressions
