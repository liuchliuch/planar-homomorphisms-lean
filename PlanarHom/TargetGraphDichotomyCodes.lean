import PlanarHom.TargetGraphDichotomyMachines
import PlanarHom.ZeroOneGraphMixedLift
import PlanarHom.ZeroOneCountSemantics
import PlanarHom.OracleReductionLaws

/-! Identical natural-answer graph codecs for planar and unrestricted input.
The independent nondeterministic verifier is reused without any planarity test. -/
noncomputable section
open Classical
set_option maxHeartbeats 1200000
namespace PlanarHom.TargetGraphDichotomy
open Complexity
open ZeroOneSharpPMembership (Relation)

/-- Every successfully decoded endpoint-valid graph word, canonical or not. -/
def ValidInput (raw : Bits) : Prop :=
  ∃ g : GraphCode, GraphCode.encoding.decode raw = some g ∧ g.Valid

/-- The unrestricted problem has the identical raw count and natural codec. -/
def unrestrictedProblem (q : ℕ) (R : Relation q) : PromiseProblem :=
  ⟨ValidInput, fun raw => BitEncoding.nat.encode (ZeroOneSharpPMembership.totalCount q R raw)⟩

/-- #P membership is one actual total accepting-path function, not a promise
oracle axiom or an assumption about graph encodings. -/
def CountingMember (P : PromiseProblem) : Prop :=
  ∃ f : Bits → ℕ, SharpP f ∧ ∀ raw, P.valid raw →
    P.value raw = BitEncoding.nat.encode (f raw)

def CountingComplete (P : PromiseProblem) : Prop :=
  CountingMember P ∧ PromisedSharpPHard P

theorem unrestricted_membership (q : ℕ) (R : Relation q) :
    CountingMember (unrestrictedProblem q R) :=
  ⟨ZeroOneSharpPMembership.totalCount q R,
    ZeroOneSharpPMembership.totalCount_sharpP q R, fun _ _ => rfl⟩

theorem planar_membership (q : ℕ) (R : Relation q) :
    CountingMember (ZeroOneSharpPMembership.planarProblem q R) :=
  ⟨ZeroOneSharpPMembership.totalCount q R,
    ZeroOneSharpPMembership.totalCount_sharpP q R, fun _ _ => rfl⟩

/-- Identity queries enlarge the allowed oracle input set. All answer bits are
charged using the already proved count-output polynomial. -/
def planar_from_unrestricted (q : ℕ) (R : Relation q) :
    PromisePolyTimeTuringReduction (ZeroOneSharpPMembership.planarProblem q R)
      (unrestrictedProblem q R) := by
  let r := PromisePolyTimeTuringReduction.refl_of_output_bound
    (unrestrictedProblem q R) (ZeroOneSharpPMembership.outputPolynomial q)
    (fun raw _ => ZeroOneSharpPMembership.totalCount_output_bound q R raw)
  refine { machine := r.machine, time := r.time, computes := ?_ }
  intro oracle ho raw hraw
  obtain ⟨g, hd, hg⟩ := hraw
  exact r.computes oracle ho raw ⟨g, hd, hg.valid⟩

theorem unrestricted_hard_of_planar (q : ℕ) (R : Relation q)
    (h : PromisedSharpPHard (ZeroOneSharpPMembership.planarProblem q R)) :
    PromisedSharpPHard (unrestrictedProblem q R) :=
  h.trans (planar_from_unrestricted q R)

private def rawView (raw : {raw // ValidInput raw}) :
    BitEncoding.ValidWord GraphCode.encoding :=
  ⟨raw.val, by obtain ⟨g, hd, _⟩ := raw.property; exact ⟨g, hd⟩⟩

private theorem rawView_valid (raw : {raw // ValidInput raw}) : (rawView raw).value.Valid := by
  obtain ⟨g, hd, hg⟩ := raw.property
  have he : (rawView raw).value = g := BitEncoding.ValidWord.value_eq hd
  rw [he]
  exact hg

/-- Actual arbitrary-raw normalization, graph-to-mixed serialization, the
unrestricted evaluator and field-to-natural extraction compose in polynomial
bit time. The proof never assumes canonical raw input. -/
theorem unrestricted_inFP_of_valid_mixed
    {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (q : ℕ) (R : Relation q)
    (h : FP (MixedCode.encoding.restrict (MixedCode.Valid 1 0)) (numberFieldEncoding basis)
      (fun g : {g : MixedCode // g.Valid 1 0} =>
        g.val.evaluate g.property (fun _ : Fin 1 => fun i j => if R i j then (1 : K) else 0)
          emptyUnaries (fun _ => 1))) :
    (unrestrictedProblem q R).InFP := by
  let input := BitEncoding.bits.restrict ValidInput
  let gv (raw : {raw // ValidInput raw}) : {g : MixedCode // g.Valid 1 0} :=
    ⟨ZeroOneMixedMembership.lift (rawView raw).value,
      ZeroOneMixedMembership.lift_valid _ (rawView_valid raw)⟩
  have hr : FP input (BitEncoding.ValidWord.encoding GraphCode.encoding) rawView :=
    fp_code_view _ _ _ (fun _ => rfl)
  have hn := (hr.comp (show FP (BitEncoding.ValidWord.encoding GraphCode.encoding)
    GraphCode.encoding BitEncoding.ValidWord.value from ⟨GraphCode.normalizer⟩)).comp
      ZeroOneMixedMembership.fp_lift
  have hl : FP input (MixedCode.encoding.restrict (MixedCode.Valid 1 0)) gv :=
    hn.transportOutput (fun _ => rfl)
  have he := (hl.comp h).comp (FieldNaturalExtraction.fp_extract basis)
  apply he.transportOutput
  intro raw
  have hv := ZeroOneMixedMembership.evaluate_lift (rawView raw).value (rawView_valid raw)
    (fun i j => if R i j then (1 : K) else 0) (fun _ => 1)
  have hc := ZeroOneSharpPMembership.totalCount_eq_evaluate (S := K) q R raw.val
    (rawView raw).value (BitEncoding.ValidWord.decode_raw (rawView raw)) (rawView_valid raw)
  have ha : (gv raw).val.evaluate (gv raw).property
      (fun _ : Fin 1 => fun i j => if R i j then (1 : K) else 0)
      emptyUnaries (fun _ => 1) =
      (ZeroOneSharpPMembership.totalCount q R raw.val : K) := hv.trans hc.symm
  change BitEncoding.nat.encode
      (FieldNaturalExtraction.extract basis ((gv raw).val.evaluate (gv raw).property
        (fun _ : Fin 1 => fun i j => if R i j then (1 : K) else 0)
        emptyUnaries (fun _ => 1))) =
    BitEncoding.nat.encode (ZeroOneSharpPMembership.totalCount q R raw.val)
  rw [ha, FieldNaturalExtraction.extract_natCast]

/-- Restricting the proved unrestricted machine gives the planar easy branch. -/
theorem planar_inFP_of_unrestricted (q : ℕ) (R : Relation q)
    (h : (unrestrictedProblem q R).InFP) :
    (ZeroOneSharpPMembership.planarProblem q R).InFP := by
  apply h.mono
  · rintro raw ⟨g, hd, hg⟩
    exact ⟨g, hd, hg.valid⟩
  · intro _ _
    rfl

end PlanarHom.TargetGraphDichotomy
