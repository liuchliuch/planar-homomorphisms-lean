import PlanarHom.TypedSourceSideCoordinates
import PlanarHom.TypedYSourceAccess
import PlanarHom.BipartiteFullTwinFinite
noncomputable section
open Classical
namespace CoreSourceCoordinateRegressions
open PlanarHom
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteContext TypedSideSourceAccess Complexity
open RectangularSourceNormSimulation (block)
variable {x y : ℕ}
theorem block_eq_crossFin (B : Matrix (Fin x) (Fin y) ℝ) : block B=crossFin B := by
  funext i j
  exact BipartiteFullTwins.fin_block_entry B i j
theorem block_crosses (B : Matrix (Fin x) (Fin y) ℝ) :
    FixedRealRootRestrictions.Bipartite.Crosses (fun _:Fin 1=>block B) (ambientSide x y) := by
  intro l i j
  refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;>
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;>
    simp [block,ambientSide]
theorem source_crosses (L : RealLanguage (x+y) 1 0) (B : Matrix (Fin x) (Fin y) ℝ)
    (hM : L.matrices 0=block B) :
    FixedRealRootRestrictions.Bipartite.Crosses L.matrices (ambientSide x y) := by
  intro l i j h
  have hl : l=0 := Subsingleton.elim _ _
  subst l
  rw [hM] at h
  exact block_crosses B 0 i j h
theorem source_contains (L : RealLanguage (x+y) 1 0) (B : Matrix (Fin x) (Fin y) ℝ)
    (hM : L.matrices 0=block B) :
    L.ContainsTypedMatrices (fun _:Fin 1=>crossPolicy) (fun _:Fin 1=>crossFin B)
      (fun _:Fin 1=>crossPolicy) := by
  refine ⟨fun _=>0,fun _=>⟨?_,rfl⟩⟩
  exact hM.trans (block_eq_crossFin B)
theorem source_algebraic (L : RealLanguage (x+y) 1 0) (B : Matrix (Fin x) (Fin y) ℝ)
    (hM : L.matrices 0=block B) :
    ∀ l:Fin 1,∀ i j,IsAlgebraic ℚ ((crossFin B) i j) := by
  intro l i j
  rw [←block_eq_crossFin B,←hM]
  exact L.matrices_algebraic 0 i j

/-- Empty color-side boundary: no positivity or nonemptiness is required for coordinates. -/
theorem empty_left (B : Matrix (Fin 0) (Fin y) ℝ) :
    crossFin B = 0 := by
  have hB : B = 0 := by funext i; exact Fin.elim0 i
  rw [hB]
  simp [crossFin]

/-- The literal Y membership is transported even for an empty opposite side. -/
theorem empty_opposite_side (F : Fin 0 → Matrix (Fin (0+y)) (Fin (0+y)) ℝ)
    (FB : Fin 0 → Fin 2 → Fin 2 → Prop) (N : Matrix (Fin y) (Fin y) ℝ) :
    N ∈ yFamily F FB ↔ N ∈ xFamily
      (fun l i j => F l (swapColors 0 y i) (swapColors 0 y j))
      (fun l a b => FB l (swapDomains a) (swapDomains b)) := by
  rw [yFamily_eq_swapped_xFamily]

/-- Empty appended Y-language still compiles into a retained context with arbitrary unaries. -/
theorem empty_y_family_source {bt ut s : ℕ}
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (L : RealLanguage (x+y) bt ut) (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀ i,L.weights i=1) (hF : L.ContainsTypedMatrices B F FB)
    (N : Fin 0→Matrix (Fin y) (Fin y) ℝ) :
    Nonempty (PromisePolyTimeTuringReduction
      (unitLanguage N (fun l=>l.elim0)).problem (L.typedProblem (domains x y) B T)) :=
  ⟨yFamily_finiteTypedReduction F FB L B T hunit hF N (fun l=>l.elim0)⟩

end CoreSourceCoordinateRegressions
