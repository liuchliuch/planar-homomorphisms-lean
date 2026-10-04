import PlanarHom.HomogeneousSourceOrientationReduction
import PlanarHom.TypedYSourceAccess

/-! NEW homogeneous original-source access for the genuine retained X/Y
families. The finite contextual compilers are composed with the constructed
ordinary-source orientation reduction, with no availability premise added. -/
noncomputable section
namespace PlanarHom.TypedSideSourceAccess
open Complexity AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteContext FixedRealRootRestrictions
variable {x y s : ℕ}

/-- Every finite ordinary X-family reduces to the literal original homogeneous
cross source. Isolates, empty inputs and original field codes are retained. -/
theorem xFamily_originalHomogeneousFiniteJointSource
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (L : RealLanguage (x+y) 1 0) (hunit : ∀ i,L.weights i=1)
    (hF : L.ContainsTypedMatrices (fun _:Fin 1=>crossPolicy) F FB)
    (hcross : Bipartite.Crosses L.matrices (ambientSide x y)) :
    FiniteJointSourceAvailable (xFamily F FB) (xFamily_algebraic F FB) L.problem :=
  xFamily_finiteJointSource F FB L (fun _:Fin 1=>crossPolicy) (fun l:Fin 0=>l.elim0)
    hunit hF L.problem (L.homogeneousUnitSourceOrientation hunit hcross)

/-- The Y-side compiler uses the same original source oracle, not a new swapped
non-hardness hypothesis or a separately supplied source algorithm. -/
theorem yFamily_originalHomogeneousFiniteJointSource
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (L : RealLanguage (x+y) 1 0) (hunit : ∀ i,L.weights i=1)
    (hF : L.ContainsTypedMatrices (fun _:Fin 1=>crossPolicy) F FB)
    (hcross : Bipartite.Crosses L.matrices (ambientSide x y)) :
    FiniteJointSourceAvailable (yFamily F FB) (yFamily_algebraic F FB) L.problem := by
  intro n N hN
  exact ⟨(yFamily_finiteTypedReduction F FB L (fun _:Fin 1=>crossPolicy)
    (fun l:Fin 0=>l.elim0) hunit hF N hN).trans
      (L.homogeneousUnitSourceOrientation hunit hcross)⟩

end PlanarHom.TypedSideSourceAccess
