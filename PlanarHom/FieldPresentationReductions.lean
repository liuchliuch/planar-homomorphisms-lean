import PlanarHom.FixedFieldEncodingTransport
import PlanarHom.NonadaptiveReductionCompiler
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.MixedEvaluationPromises
import PlanarHom.MixedTotalEvaluation
import PlanarHom.MixedEvaluationFieldMap

/-! Actual fixed-field output-presentation reductions. Every query is the original
raw bitword. Real ordinary machines convert answers, with full bit-cost charging. -/
noncomputable section
namespace PlanarHom.Complexity
open PlanarHom.FixedFieldEncodingTransport

/-- One unchanged raw query followed by an actual answer-conversion machine. -/
noncomputable def sameQueryOutputReduction
    {K L : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (bK : Module.Basis (Fin d) ℚ K) (eL : BitEncoding L)
    (target source : PromiseProblem) (answer : Bits → K) (f : K → L)
    (hf : FP (numberFieldEncoding bK) eL f)
    (hvalid : ∀ raw, target.valid raw → source.valid raw)
    (hanswer : ∀ raw, source.valid raw → source.value raw = (numberFieldEncoding bK).encode (answer raw))
    (hcorrect : ∀ raw, target.valid raw → eL.encode (f (answer raw)) = target.value raw)
    (p : Polynomial ℕ) (hsize : ∀ raw, source.valid raw → (source.value raw).length ≤ p.eval raw.length) :
    PromisePolyTimeTuringReduction target source := by
  let prepare : Bits → Bits × List Bits := fun raw => ([], [raw])
  let recover : Bits × List K → L := fun data => f data.2.sum
  have hp : FP BitEncoding.bits (BitEncoding.bits.prod BitEncoding.bits.list) prepare := by
    have hs := ((fp_id BitEncoding.bits).pair (fp_const BitEncoding.bits BitEncoding.bits.list [])).comp
      (PlanarHom.ListMutationMachines.fp_cons BitEncoding.bits)
    exact (fp_const BitEncoding.bits BitEncoding.bits []).pair hs
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding bK).list) eL recover :=
    ((PairProjectionMachines.fp_snd BitEncoding.bits (numberFieldEncoding bK).list).comp
      (PlanarHom.MaterializedFieldListMachines.fp_sum bK)).comp hf
  apply nonadaptiveReduction BitEncoding.bits BitEncoding.bits BitEncoding.bits
    (numberFieldEncoding bK) eL target source prepare answer recover
    (Classical.choice hp) (Classical.choice hr) (fun raw _ => raw) (fun _ _ => rfl)
  · intro raw h query hq
    have he : query = raw := List.mem_singleton.mp hq
    subst query
    exact hvalid raw h
  · exact hanswer
  · intro raw h
    simpa only [prepare, recover, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero] using hcorrect raw h
  · exact hsize

end PlanarHom.Complexity

namespace PlanarHom.Complexity.MixedCode
open PlanarHom.FixedFieldEncodingTransport
variable {C K L : Type} [Fintype C] [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
variable {d e bt ut : ℕ}

def decodedEvaluation (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (raw : Bits) : K :=
  match encoding.decode raw with
  | none => 0
  | some g => totalEvaluation M U w g

theorem evaluationValue_eq_decoded (basis : Module.Basis (Fin d) ℚ K)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (raw : Bits) (h : PlanarInput bt ut raw) :
    evaluationValue basis M U w raw = (numberFieldEncoding basis).encode (decodedEvaluation M U w raw) := by
  obtain ⟨g, hd, hg⟩ := h
  rw [evaluationValue_decode basis M U w raw g hd hg.1]
  simp only [decodedEvaluation, hd, totalEvaluation_valid M U w g hg.1]

omit [Algebra ℚ K] [Algebra ℚ L] in
theorem map_decodedEvaluation (φ : K →+* L)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (raw : Bits) (h : PlanarInput bt ut raw) :
    φ (decodedEvaluation M U w raw) =
      decodedEvaluation (fun l i j => φ (M l i j)) (fun l i => φ (U l i)) (fun i => φ (w i)) raw := by
  obtain ⟨g, hd, hg⟩ := h
  simp only [decodedEvaluation, hd, totalEvaluation_valid _ _ _ g hg.1]
  exact map_evaluate φ g hg.1 M U w

/-- The original raw promise is retained without imposing canonical inputs. -/
noncomputable def fieldMapReductionOn (bK : Module.Basis (Fin d) ℚ K)
    (bL : Module.Basis (Fin e) ℚ L) (φ : K →ₐ[ℚ] L)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (P : Bits → Prop) (hP : ∀ raw, P raw → PlanarInput bt ut raw) :
    PromisePolyTimeTuringReduction
      ⟨P, evaluationValue bL (fun l i j => φ (M l i j)) (fun l i => φ (U l i)) (fun i => φ (w i))⟩
      ⟨P, evaluationValue bK M U w⟩ := by
  let bound := evaluationProblem_output_bound bK M U w
  let p := Classical.choose bound
  have hp := Classical.choose_spec bound
  apply sameQueryOutputReduction bK (numberFieldEncoding bL)
    ⟨P, evaluationValue bL (fun l i j => φ (M l i j)) (fun l i => φ (U l i)) (fun i => φ (w i))⟩
    ⟨P, evaluationValue bK M U w⟩
    (decodedEvaluation M U w) φ (fp_fieldEmbedding bK bL φ) (fun _ h => h) (p := p)
  · intro raw h
    exact evaluationValue_eq_decoded bK M U w raw (hP raw h)
  · intro raw h
    have hm : φ (decodedEvaluation M U w raw) = decodedEvaluation (fun l i j => φ (M l i j))
        (fun l i => φ (U l i)) (fun i => φ (w i)) raw :=
      map_decodedEvaluation φ.toRingHom M U w raw (hP raw h)
    rw [hm]
    exact (evaluationValue_eq_decoded bL _ _ _ raw (hP raw h)).symm
  · exact fun raw h => hp raw (hP raw h)

/-- The linear retraction is only used on answers in the true embedded field. -/
noncomputable def fieldDescentReductionOn (bK : Module.Basis (Fin d) ℚ K)
    (bL : Module.Basis (Fin e) ℚ L) (φ : K →ₐ[ℚ] L)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (P : Bits → Prop) (hP : ∀ raw, P raw → PlanarInput bt ut raw) :
    PromisePolyTimeTuringReduction ⟨P, evaluationValue bK M U w⟩
      ⟨P, evaluationValue bL (fun l i j => φ (M l i j)) (fun l i => φ (U l i)) (fun i => φ (w i))⟩ := by
  let inverse := exists_fp_leftInverse bK bL φ.toLinearMap φ.injective
  let g := Classical.choose inverse
  have hg := (Classical.choose_spec inverse).1
  have hfp := (Classical.choose_spec inverse).2
  let bound := evaluationProblem_output_bound bL
    (fun l i j => φ (M l i j)) (fun l i => φ (U l i)) (fun i => φ (w i))
  let p := Classical.choose bound
  have hp := Classical.choose_spec bound
  apply sameQueryOutputReduction bL (numberFieldEncoding bK)
    ⟨P, evaluationValue bK M U w⟩
    ⟨P, evaluationValue bL (fun l i j => φ (M l i j)) (fun l i => φ (U l i)) (fun i => φ (w i))⟩
    (decodedEvaluation (fun l i j => φ (M l i j)) (fun l i => φ (U l i)) (fun i => φ (w i))) g hfp
    (fun _ h => h) (p := p)
  · intro raw h
    exact evaluationValue_eq_decoded bL _ _ _ raw (hP raw h)
  · intro raw h
    have hm : φ (decodedEvaluation M U w raw) = decodedEvaluation (fun l i j => φ (M l i j))
        (fun l i => φ (U l i)) (fun i => φ (w i)) raw :=
      map_decodedEvaluation φ.toRingHom M U w raw (hP raw h)
    rw [← hm]
    rw [show g (φ (decodedEvaluation M U w raw)) = decodedEvaluation M U w raw from hg _]
    exact (evaluationValue_eq_decoded bK M U w raw (hP raw h)).symm
  · exact fun raw h => hp raw (hP raw h)

noncomputable def fieldMapReduction (bK : Module.Basis (Fin d) ℚ K)
    (bL : Module.Basis (Fin e) ℚ L) (φ : K →ₐ[ℚ] L)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K) :=
  fieldMapReductionOn bK bL φ M U w (PlanarInput bt ut) (fun _ h => h)

noncomputable def fieldDescentReduction (bK : Module.Basis (Fin d) ℚ K)
    (bL : Module.Basis (Fin e) ℚ L) (φ : K →ₐ[ℚ] L)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K) :=
  fieldDescentReductionOn bK bL φ M U w (PlanarInput bt ut) (fun _ h => h)

/-- Domain metadata, endpoint typing and every original raw word are unchanged. -/
noncomputable def domainFieldMapReduction {dt : ℕ}
    (bK : Module.Basis (Fin d) ℚ K) (bL : Module.Basis (Fin e) ℚ L) (φ : K →ₐ[ℚ] L)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem bL (fun l i j => φ (M l i j)) (fun l i => φ (U l i))
        (fun i => φ (w i)) D B T)
      (domainEvaluationProblem bK M U w D B T) := by
  have h := fieldMapReductionOn bK bL φ M (PlanarHom.PrescribedDomains.extendedUnaries U D) w
    (PlanarHom.PrescribedDomains.EncodedInput B T) (fun _ h => h.planarInput)
  have hext : (fun l i => φ (PlanarHom.PrescribedDomains.extendedUnaries U D l i)) =
      PlanarHom.PrescribedDomains.extendedUnaries (fun l i => φ (U l i)) D :=
    PlanarHom.PrescribedDomains.map_extendedUnaries φ.toRingHom U D
  simpa only [domainEvaluationProblem, hext] using h

noncomputable def domainFieldDescentReduction {dt : ℕ}
    (bK : Module.Basis (Fin d) ℚ K) (bL : Module.Basis (Fin e) ℚ L) (φ : K →ₐ[ℚ] L)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem bK M U w D B T)
      (domainEvaluationProblem bL (fun l i j => φ (M l i j)) (fun l i => φ (U l i))
        (fun i => φ (w i)) D B T) := by
  have h := fieldDescentReductionOn bK bL φ M (PlanarHom.PrescribedDomains.extendedUnaries U D) w
    (PlanarHom.PrescribedDomains.EncodedInput B T) (fun _ h => h.planarInput)
  have hext : (fun l i => φ (PlanarHom.PrescribedDomains.extendedUnaries U D l i)) =
      PlanarHom.PrescribedDomains.extendedUnaries (fun l i => φ (U l i)) D :=
    PlanarHom.PrescribedDomains.map_extendedUnaries φ.toRingHom U D
  simpa only [domainEvaluationProblem, hext] using h

end PlanarHom.Complexity.MixedCode
