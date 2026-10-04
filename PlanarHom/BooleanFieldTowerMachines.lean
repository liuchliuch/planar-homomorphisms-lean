import PlanarHom.BooleanFieldTower
import PlanarHom.FixedFieldPolynomialMachines

/-! Every fixed-dimensional reduced tower operation is compiled from actual
fixed-field arithmetic circuits. The dimension is compile-time data. -/
noncomputable section
namespace PlanarHom.BooleanFieldTowerMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines BooleanFieldTower
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def encoding : (n : ℕ) → BitEncoding (Tower K n)
  | 0 => numberFieldEncoding basis
  | n+1 => (encoding n).prod (encoding n)

variable {α : Type} (ea : BitEncoding α)

theorem fp_embed (n : ℕ) (f : α → K) (hf : FP ea (numberFieldEncoding basis) f) :
    FP ea (encoding basis n) (fun x => embed n (f x)) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.pair (fp_const ea (encoding basis n) (zero n))

theorem fp_add (n : ℕ) (p q : α → Tower K n)
    (hp : FP ea (encoding basis n) p) (hq : FP ea (encoding basis n) q) :
    FP ea (encoding basis n) (fun x => add n (p x) (q x)) := by
  induction n with
  | zero => exact (hp.pair hq).comp (FixedFieldArithmetic.fp_addition basis)
  | succ n ih =>
    have hpr := hp.comp (fp_fst (encoding basis n) (encoding basis n))
    have hpi := hp.comp (fp_snd (encoding basis n) (encoding basis n))
    have hqr := hq.comp (fp_fst (encoding basis n) (encoding basis n))
    have hqi := hq.comp (fp_snd (encoding basis n) (encoding basis n))
    exact (ih _ _ hpr hqr).pair (ih _ _ hpi hqi)

theorem fp_neg (n : ℕ) (p : α → Tower K n) (hp : FP ea (encoding basis n) p) :
    FP ea (encoding basis n) (fun x => neg n (p x)) := by
  induction n with
  | zero => exact hp.comp (FixedFieldArithmetic.fp_negation basis)
  | succ n ih =>
    exact (ih _ (hp.comp (fp_fst (encoding basis n) (encoding basis n)))).pair
      (ih _ (hp.comp (fp_snd (encoding basis n) (encoding basis n))))

theorem fp_sub (n : ℕ) (p q : α → Tower K n)
    (hp : FP ea (encoding basis n) p) (hq : FP ea (encoding basis n) q) :
    FP ea (encoding basis n) (fun x => sub n (p x) (q x)) :=
  fp_add basis ea n p _ hp (fp_neg basis ea n q hq)

theorem fp_mul (D : α → ℕ → K) (hD : ∀ i, FP ea (numberFieldEncoding basis) (fun x => D x i))
    (n : ℕ) (p q : α → Tower K n)
    (hp : FP ea (encoding basis n) p) (hq : FP ea (encoding basis n) q) :
    FP ea (encoding basis n) (fun x => mul (D x) n (p x) (q x)) := by
  induction n with
  | zero => exact (hp.pair hq).comp (FixedFieldArithmetic.fp_multiplication basis)
  | succ n ih =>
    have hpr := hp.comp (fp_fst (encoding basis n) (encoding basis n))
    have hpi := hp.comp (fp_snd (encoding basis n) (encoding basis n))
    have hqr := hq.comp (fp_fst (encoding basis n) (encoding basis n))
    have hqi := hq.comp (fp_snd (encoding basis n) (encoding basis n))
    have hd := fp_embed basis ea n _ (hD n)
    exact (fp_add basis ea n _ _ (ih _ _ hpr hqr) (ih _ _ hd (ih _ _ hpi hqi))).pair
      (fp_add basis ea n _ _ (ih _ _ hpr hqi) (ih _ _ hpi hqr))

theorem fp_norm (D : α → ℕ → K) (hD : ∀ i, FP ea (numberFieldEncoding basis) (fun x => D x i))
    (n : ℕ) (p : α → Tower K n) (hp : FP ea (encoding basis n) p) :
    FP ea (numberFieldEncoding basis) (fun x => norm (D x) n (p x)) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    have hpr := hp.comp (fp_fst (encoding basis n) (encoding basis n))
    have hpi := hp.comp (fp_snd (encoding basis n) (encoding basis n))
    have hd := fp_embed basis ea n _ (hD n)
    apply ih
    exact fp_sub basis ea n _ _ (fp_mul basis ea D hD n _ _ hpr hpr)
      (fp_mul basis ea D hD n _ _ hd (fp_mul basis ea D hD n _ _ hpi hpi))

theorem fp_linear (n : ℕ) (i : Fin n) (e o : α → K)
    (he : FP ea (numberFieldEncoding basis) e) (ho : FP ea (numberFieldEncoding basis) o) :
    FP ea (encoding basis n) (fun x => linear n i (e x) (o x)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [linear,Fin.lastCases_last] using
        (fp_embed basis ea n e he).pair (fp_embed basis ea n o ho)
    · simpa only [linear,Fin.lastCases_castSucc] using
        (ih j).pair (fp_const ea (encoding basis n) (zero n))

theorem fp_product (D : α → ℕ → K) (hD : ∀ i, FP ea (numberFieldEncoding basis) (fun x => D x i))
    (n k : ℕ) (f : Fin k → α → Tower K n)
    (hf : ∀ i, FP ea (encoding basis n) (f i)) :
    FP ea (encoding basis n) (fun x => product (D x) n k (fun i => f i x)) := by
  induction k with
  | zero => exact fp_const ea (encoding basis n) (embed n 1)
  | succ k ih => exact fp_mul basis ea D hD n _ _ (ih _ (fun i => hf i.castSucc)) (hf (Fin.last k))

end PlanarHom.BooleanFieldTowerMachines
