import PlanarHom.FixedRealCoordinateDescent

/-! NEW: iterate the actual coefficient descent through any fixed number of
extra variables. All coordinate denominators remain shared at every step. -/
noncomputable section
namespace PlanarHom.FixedRealVariableTowerDescent
open DensePolynomial Complexity

def inclusion (c : ℕ) : (b : ℕ) → RationalFunction c →+* RationalFunction (c+b)
  | 0 => RingHom.id _
  | b+1 => (DenseOuterVariableDescent.inclusion (c+b)).comp (inclusion c b)

def run (c e : ℕ) : (b : ℕ) → FixedRealExtension.Code (c+b) e → FixedRealExtension.Code c e
  | 0,a => a
  | b+1,a => run c e b (FixedRealCoordinateDescent.run (c+b) e a)

theorem fp_run (c e b : ℕ) : FP (FixedRealExtension.encoding (c+b) e)
    (FixedRealExtension.encoding c e) (run c e b) := by
  induction b with
  | zero => exact fp_id _
  | succ b ih => exact (FixedRealCoordinateDescent.fp_run (c+b) e).comp ih

theorem run_valid (c e b : ℕ) (a : FixedRealExtension.Code (c+b) e)
    (ha : FixedRealExtension.Valid (c+b) a) : FixedRealExtension.Valid c (run c e b a) := by
  induction b with
  | zero => exact ha
  | succ b ih => exact ih _ (FixedRealCoordinateDescent.run_valid (c+b) e a ha)

theorem coordinates_run_known (c e b : ℕ) (a : FixedRealExtension.Code (c+b) e)
    (ha : FixedRealExtension.Valid (c+b) a) (r : Fin e → RationalFunction c)
    (hr : FixedRealExtension.coordinates (c+b) a = fun i => inclusion c b (r i)) :
    FixedRealExtension.coordinates c (run c e b a) = r := by
  induction b with
  | zero => exact hr
  | succ b ih =>
    apply ih _ (FixedRealCoordinateDescent.run_valid (c+b) e a ha)
    funext i
    exact DenseOuterVariableDescent.descendFraction_value (c+b) (a.1 i,a.2) ha
      (inclusion c b (r i)) (congrFun hr i)

variable {c e b : ℕ} {F E : Type} [Field F] [Field E]
  [Algebra (RationalFunction c) F] [Algebra (RationalFunction (c+b)) E]

structure Compatible
    (lower : Module.Basis (Fin e) (RationalFunction c) F)
    (upper : Module.Basis (Fin e) (RationalFunction (c+b)) E) (embed : F →+* E) : Prop where
  scalar : ∀ r, embed (algebraMap (RationalFunction c) F r) =
    algebraMap (RationalFunction (c+b)) E (inclusion c b r)
  basis : ∀ i, embed (lower i) = upper i

theorem coordinates_embed
    (lower : Module.Basis (Fin e) (RationalFunction c) F)
    (upper : Module.Basis (Fin e) (RationalFunction (c+b)) E) (embed : F →+* E)
    (h : Compatible lower upper embed) (z : F) :
    upper.equivFun (embed z) = fun i => inclusion c b (lower.equivFun z i) := by
  have hz : embed z = ∑ i, inclusion c b (lower.equivFun z i) • upper i := by
    conv_lhs => rw [← lower.sum_equivFun z]
    simp only [map_sum,Algebra.smul_def,map_mul,h.scalar,h.basis]
  rw [hz]
  have hs := upper.sum_equivFun (upper.equivFun.symm (fun i => inclusion c b (lower.equivFun z i)))
  simpa only [upper.equivFun.apply_symm_apply] using congrArg upper.equivFun hs

theorem value_run_known
    (lower : Module.Basis (Fin e) (RationalFunction c) F)
    (upper : Module.Basis (Fin e) (RationalFunction (c+b)) E) (embed : F →+* E)
    (h : Compatible lower upper embed) (a : FixedRealExtension.Code (c+b) e)
    (ha : FixedRealExtension.Valid (c+b) a) (z : F)
    (hz : FixedRealExtension.value upper a = embed z) :
    FixedRealExtension.value lower (run c e b a) = z := by
  have hc := congrArg upper.equivFun hz
  rw [coordinates_embed lower upper embed h z] at hc
  simp only [FixedRealExtension.value,upper.equivFun.apply_symm_apply] at hc
  apply lower.equivFun.injective
  simpa only [FixedRealExtension.value,lower.equivFun.apply_symm_apply] using
    coordinates_run_known c e b a ha (lower.equivFun z) hc

end PlanarHom.FixedRealVariableTowerDescent
