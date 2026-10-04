import PlanarHom.BooleanFieldTowerReconstruction
import PlanarHom.BooleanFieldTowerMachines

/-! Fixed-dimensional radical inversion has genuine polynomial bit cost: the
compiler uses the frozen base-field machines, framed-pair projections, and
composition. Dimension is a fixed parameter, never part of the input. -/
noncomputable section
namespace PlanarHom.BooleanFieldTowerInverseMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open BooleanFieldTower BooleanFieldTowerInverse BooleanFieldTowerMachines
open BooleanFieldTowerReconstruction
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)
variable {α : Type} (ea : BitEncoding α)

/-- Recursive conjugation, followed at the leaf by exact base-field inversion. -/
theorem fp_inverse (D : α → ℕ → K)
    (hD : ∀ i, FP ea (numberFieldEncoding basis) (fun x => D x i))
    (n : ℕ) (p : α → Tower K n) (hp : FP ea (encoding basis n) p) :
    FP ea (encoding basis n) (fun x => inverse (D x) n (p x)) := by
  induction n with
  | zero => exact hp.comp (FixedFieldArithmetic.fp_inverse basis)
  | succ n ih =>
    have hpr := hp.comp (fp_fst (encoding basis n) (encoding basis n))
    have hpi := hp.comp (fp_snd (encoding basis n) (encoding basis n))
    have hd := fp_embed basis ea n _ (hD n)
    have hnorm := fp_sub basis ea n _ _ (fp_mul basis ea D hD n _ _ hpr hpr)
      (fp_mul basis ea D hD n _ _ hd (fp_mul basis ea D hD n _ _ hpi hpi))
    have hq := ih _ hnorm
    exact (fp_mul basis ea D hD n _ _ hpr hq).pair
      (fp_neg basis ea n _ (fp_mul basis ea D hD n _ _ hpi hq))

/-- Extraction of the invariant base value is a fixed sequence of projections. -/
theorem fp_constantCoeff (n : ℕ) (p : α → Tower K n)
    (hp : FP ea (encoding basis n) p) :
    FP ea (numberFieldEncoding basis) (fun x => constantCoeff n (p x)) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact ih _ (hp.comp (fp_fst (encoding basis n) (encoding basis n)))

/-- Every selected squarefree coefficient is obtained by fixed tuple projections. -/
theorem fp_coefficient (n : ℕ) (p : α → Tower K n)
    (hp : FP ea (encoding basis n) p) (σ : Fin n → Bool) :
    FP ea (numberFieldEncoding basis) (fun x => coefficient n (p x) σ) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    cases hs : σ (Fin.last n)
    · simpa only [coefficient,hs,Bool.false_eq_true,↓reduceIte] using
        ih _ (hp.comp (fp_fst (encoding basis n) (encoding basis n))) (fun i=>σ i.castSucc)
    · simpa only [coefficient,hs,↓reduceIte] using
        ih _ (hp.comp (fp_snd (encoding basis n) (encoding basis n))) (fun i=>σ i.castSucc)

end PlanarHom.BooleanFieldTowerInverseMachines
