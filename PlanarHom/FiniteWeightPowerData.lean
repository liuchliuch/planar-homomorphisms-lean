import PlanarHom.DiagonalRationalPowerCompatibility
import PlanarHom.AlgebraicFiniteProductInterpolation

/-! Literal finite families of positive weight powers and the exact source
product maps from inverse diagonal and inverse unary entries. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveWeightRemoval
open AlgebraicProductInterpolation ProductCompatibility FiniteLanguageAliases
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀] {q n : ℕ}

def finitePowerDiagonals (w : Fin q→K₀) (rs : Fin n→ℚ) : Fin n→Matrix (Fin q) (Fin q) ℝ :=
  fun l=>diagonalPower (fun i=>(w i : ℝ)) (rs l)
def finitePowerUnaries (w : Fin q→K₀) (rs : Fin n→ℚ) : Fin n→Fin q→ℝ :=
  fun l i=>(w i : ℝ)^(rs l : ℝ)

theorem finitePowerDiagonals_algebraic (w : Fin q→K₀) (hw : ∀i,0<(w i : ℝ)) (rs : Fin n→ℚ) :
    ∀l i j,IsAlgebraic ℚ (finitePowerDiagonals w rs l i j) :=
  fun l=>diagonalPower_algebraic _ hw (fun i=>(Algebra.IsAlgebraic.isAlgebraic (w i)).algHom K₀.val) (rs l)

theorem finitePowerUnaries_algebraic (w : Fin q→K₀) (hw : ∀i,0<(w i : ℝ)) (rs : Fin n→ℚ) :
    ∀l i,IsAlgebraic ℚ (finitePowerUnaries w rs l i) :=
  fun l i=>PositiveUnaryRationalPowers.isAlgebraic_real_rpow_rat (hw i)
    ((Algebra.IsAlgebraic.isAlgebraic (w i)).algHom K₀.val) (rs l)

theorem inverseUnary_productMaps (w : Fin q→K₀) (hw : ∀i,0<(w i : ℝ)) (r : ℚ) :
    HasProductMaps (fun i=>((w i)⁻¹ : K₀).val) (fun i=>(w i : ℝ)^(r:ℝ)) := by
  have he : (fun i=>((w i : ℝ)⁻¹)^(-(r:ℝ)))=(fun i=>(w i : ℝ)^(r:ℝ)) := by
    funext i
    rw [Real.inv_rpow (hw i).le,Real.rpow_neg (hw i).le,inv_inv]
  simpa only [he] using PositiveUnaryRationalPowers.hasProductMaps_real_rpow
    (fun i=>(w i : ℝ)⁻¹) (fun i=>inv_pos.mpr (hw i)) (-(r:ℝ))

theorem inverseDiagonal_coe (w : Fin q→K₀) (i j : Fin q) :
    (Matrix.diagonal (fun i=>(w i)⁻¹) i j : ℝ)=Matrix.diagonal (fun i=>(w i : ℝ)⁻¹) i j := by
  by_cases h:i=j
  · subst j; simp only [Matrix.diagonal_apply_eq]; rfl
  · simp [Matrix.diagonal_apply,h]

theorem inverseDiagonal_productMaps (w : Fin q→K₀) (hw : ∀i,0<(w i : ℝ)) (r : ℚ) :
    HasProductMaps (fun p : Fin q×Fin q=>(Matrix.diagonal (fun i=>(w i)⁻¹) p.1 p.2 : ℝ))
      (fun p=>diagonalPower (fun i=>(w i : ℝ)) r p.1 p.2) := by
  simp only [inverseDiagonal_coe]
  exact hasProductMaps_of_compatible _ _ (diagonalPower_compatible _ hw r)

theorem appendOne_map {α β : Type} {b : ℕ} (f : α→β) (M : Fin b→α) (a : α) :
    f ∘ appendOne M a=appendOne (f ∘ M) (f a) := by
  funext l
  refine Fin.lastCases ?_ (fun i=>?_) l
  · simp only [Function.comp_apply,appendOne_aux]
  · change f (appendOne M a (Fin.castAdd 1 i))=appendOne (f ∘ M) (f a) (Fin.castAdd 1 i)
    simp only [appendOne_old,Function.comp_apply]

end PlanarHom.PositiveWeightRemoval
