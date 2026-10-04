import PlanarHom.FixedRealTraceMachines
import PlanarHom.ListFilterMachines
import PlanarHom.ListIndexMachines
import PlanarHom.OccurrencePfaffianListPrimitives

/-! NEW: an exact nonzero-denominator coefficient scan with compiled bit cost.
The selected coefficient may occur after arbitrarily many zero padding entries. -/
noncomputable section
namespace PlanarHom.DenseCoefficientSelection
open DensePolynomial Complexity PairProjectionMachines

def nonzeroTerms (d : ℕ) (q : DensePolynomial.Code (d+1)) :
    List (DensePolynomial.Code d × ℕ) := q.zipIdx.filter (fun p => !isZero d p.1)

def pick (d : ℕ) (q : DensePolynomial.Code (d+1)) : DensePolynomial.Code d × ℕ :=
  (nonzeroTerms d q).headD (zero d,0)

def coefficient (d : ℕ) (q : DensePolynomial.Code (d+1)) (k : ℕ) : DensePolynomial.Code d :=
  q[k]?.getD (zero d)

theorem fp_pick (d : ℕ) : FP (encoding (d+1)) ((encoding d).prod BitEncoding.nat) (pick d) := by
  let ep := (encoding d).prod BitEncoding.nat
  have hz := (fp_fst (encoding d) BitEncoding.nat).comp (DensePolynomial.fp_isZero d)
  have hp := (hz.pair hz).comp
    (ArithmeticCircuitPrimitives.fp_bool_gate (fun p => !p.1))
  exact ((ListIndexMachines.fp_zipIdx (encoding d)).comp
    (ListFilterMachines.fp_filter ep (fun p => !isZero d p.1) hp)).comp
      (ListDecompositionMachines.fp_headD ep (zero d,0))

theorem fp_coefficient (d : ℕ) : FP ((encoding (d+1)).prod BitEncoding.nat)
    (encoding d) (fun p => coefficient d p.1 p.2) := PfaffianList.fp_at (encoding d) (zero d)

theorem nonzeroTerms_ne_nil (d : ℕ) (q : DensePolynomial.Code (d+1))
    (hq : interpret (d+1) q ≠ 0) : nonzeroTerms d q ≠ [] := by
  intro hz
  apply hq
  apply Polynomial.ext
  intro k
  rw [interpret_coeff]
  cases hk : q[k]? with
  | none => simp [hk]
  | some a =>
    have hm : (a,k) ∈ q.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hk
    have ha : isZero d a = true := by
      by_contra hn
      have hf : (a,k) ∈ nonzeroTerms d q := List.mem_filter.mpr ⟨hm,by simpa using hn⟩
      rw [hz] at hf
      exact List.not_mem_nil hf
    simpa only [hk,Option.getD_some,Polynomial.coeff_zero] using (isZero_iff d a).mp ha

theorem pick_spec (d : ℕ) (q : DensePolynomial.Code (d+1))
    (hq : interpret (d+1) q ≠ 0) :
    q[(pick d q).2]? = some (pick d q).1 ∧ interpret d (pick d q).1 ≠ 0 := by
  have hn := nonzeroTerms_ne_nil d q hq
  have hm : pick d q ∈ nonzeroTerms d q := by
    unfold pick
    cases h : nonzeroTerms d q with
    | nil => exact (hn h).elim
    | cons a xs => simp
  obtain ⟨hi,hz⟩ := List.mem_filter.mp hm
  refine ⟨List.mem_zipIdx_iff_getElem?.mp hi,?_⟩
  intro hzero
  have hz' := (isZero_iff d (pick d q).1).mpr hzero
  simp only [hz',Bool.not_true, Bool.false_eq_true] at hz

def descendFraction (d : ℕ) (a : FractionCode (d+1)) : FractionCode d :=
  (coefficient d a.1 (pick d a.2).2,(pick d a.2).1)

theorem fp_descendFraction (d : ℕ) : FP (fractionEncoding (d+1)) (fractionEncoding d)
    (descendFraction d) := by
  let ep := encoding (d+1)
  have hp := (fp_snd ep ep).comp (fp_pick d)
  have hk := hp.comp (fp_snd (encoding d) BitEncoding.nat)
  have hn := ((fp_fst ep ep).pair hk).comp (fp_coefficient d)
  exact hn.pair (hp.comp (fp_fst (encoding d) BitEncoding.nat))

theorem descendFraction_valid (d : ℕ) (a : FractionCode (d+1))
    (ha : FractionValid (d+1) a) : FractionValid d (descendFraction d a) :=
  (pick_spec d a.2 ha).2

end PlanarHom.DenseCoefficientSelection
