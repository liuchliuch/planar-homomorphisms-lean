import PlanarHom.TypedHomogeneousCommonCharts
import PlanarHom.BipartiteFullTwinFinite

/-! Exact surviving original source-coordinate proofs, with source-closed imports. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularCoreSourceEntrance
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteContext TypedSideSourceAccess ClosedMatrixFamily Complexity
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
end PlanarHom.RectangularCoreSourceEntrance
