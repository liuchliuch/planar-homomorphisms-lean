import PlanarHom.DenseOuterVariableDescent

/-! NEW: one shared coefficient scan removes an outer transcendence variable
from every finite-extension coordinate. Compatibility states only the actual
field embeddings and fixed bases, never a supplied conversion algorithm. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealCoordinateDescent
open DensePolynomial DenseCoefficientSelection Complexity PairProjectionMachines RepresentedBit

def run (d e : ℕ) (a : FixedRealExtension.Code (d+1) e) : FixedRealExtension.Code d e :=
  (fun i => coefficient d (a.1 i) (pick d a.2).2,(pick d a.2).1)

theorem fp_run (d e : ℕ) :
    FP (FixedRealExtension.encoding (d+1) e) (FixedRealExtension.encoding d e) (run d e) := by
  let ep := encoding (d+1)
  let ei := (ep.vector e).prod ep
  have hp := (fp_snd (ep.vector e) ep).comp (fp_pick d)
  have hk := hp.comp (fp_snd (encoding d) BitEncoding.nat)
  have hn : FP ei ((encoding d).vector e) (fun a i => coefficient d (a.1 i) (pick d a.2).2) := by
    apply FixedVectorMachines.fp_assemble
    intro i
    have ha := (fp_fst (ep.vector e) ep).comp (FixedVectorMachines.fp_coordinate ep e i)
    exact (ha.pair hk).comp (fp_coefficient d)
  exact hn.pair (hp.comp (fp_fst (encoding d) BitEncoding.nat))

theorem run_valid (d e : ℕ) (a : FixedRealExtension.Code (d+1) e)
    (ha : FixedRealExtension.Valid (d+1) a) : FixedRealExtension.Valid d (run d e a) :=
  (pick_spec d a.2 ha).2

variable {d e : ℕ} {F E : Type} [Field F] [Field E]
  [Algebra (RationalFunction d) F] [Algebra (RationalFunction (d+1)) E]

structure Compatible
    (lower : Module.Basis (Fin e) (RationalFunction d) F)
    (upper : Module.Basis (Fin e) (RationalFunction (d+1)) E) (embed : F →+* E) : Prop where
  scalar : ∀ r : RationalFunction d, embed (algebraMap (RationalFunction d) F r) =
    algebraMap (RationalFunction (d+1)) E (DenseOuterVariableDescent.inclusion d r)
  basis : ∀ i, embed (lower i) = upper i

theorem coordinates_embed
    (lower : Module.Basis (Fin e) (RationalFunction d) F)
    (upper : Module.Basis (Fin e) (RationalFunction (d+1)) E) (embed : F →+* E)
    (h : Compatible lower upper embed) (z : F) :
    upper.equivFun (embed z) = fun i => DenseOuterVariableDescent.inclusion d (lower.equivFun z i) := by
  have hz : embed z = ∑ i, DenseOuterVariableDescent.inclusion d (lower.equivFun z i) • upper i := by
    conv_lhs => rw [← lower.sum_equivFun z]
    simp only [map_sum, Algebra.smul_def, map_mul, h.scalar, h.basis]
  rw [hz]
  have hs := upper.sum_equivFun
    (upper.equivFun.symm (fun i => DenseOuterVariableDescent.inclusion d (lower.equivFun z i)))
  simpa only [upper.equivFun.apply_symm_apply] using congrArg upper.equivFun hs

theorem value_run_known
    (lower : Module.Basis (Fin e) (RationalFunction d) F)
    (upper : Module.Basis (Fin e) (RationalFunction (d+1)) E) (embed : F →+* E)
    (h : Compatible lower upper embed) (a : FixedRealExtension.Code (d+1) e)
    (ha : FixedRealExtension.Valid (d+1) a) (z : F)
    (hz : FixedRealExtension.value upper a = embed z) :
    FixedRealExtension.value lower (run d e a) = z := by
  have hc := congrArg upper.equivFun hz
  rw [coordinates_embed lower upper embed h z] at hc
  simp only [FixedRealExtension.value, upper.equivFun.apply_symm_apply] at hc
  apply lower.equivFun.injective
  simp only [FixedRealExtension.value, lower.equivFun.apply_symm_apply]
  funext i
  exact DenseOuterVariableDescent.descendFraction_value d (a.1 i,a.2) ha
    (lower.equivFun z i) (congrFun hc i)

def descentProblem
    (lower : Module.Basis (Fin e) (RationalFunction d) F)
    (upper : Module.Basis (Fin e) (RationalFunction (d+1)) E) (embed : F →+* E) : Problem :=
  typedProblem (FixedRealExtension.encoding (d+1) e) (FixedRealExtension.encoding d e)
    (fun a => FixedRealExtension.Valid (d+1) a ∧ ∃ z, FixedRealExtension.value upper a = embed z)
    (fun a b => FixedRealExtension.Valid d b ∧ embed (FixedRealExtension.value lower b) =
      FixedRealExtension.value upper a)

theorem descent_inFP
    (lower : Module.Basis (Fin e) (RationalFunction d) F)
    (upper : Module.Basis (Fin e) (RationalFunction (d+1)) E) (embed : F →+* E)
    (h : Compatible lower upper embed) : (descentProblem lower upper embed).InFP := by
  apply typedProblem_inFP _ _ (FixedRealExtension.normalizer (d+1) e) _ _
    (run d e) (fp_run d e)
  intro a ha
  obtain ⟨z,hz⟩ := ha.2
  exact ⟨run_valid d e a ha.1, by rw [value_run_known lower upper embed h a ha.1 z hz, hz]⟩

end PlanarHom.FixedRealCoordinateDescent
