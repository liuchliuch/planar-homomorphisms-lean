-- Recovered theorem bodies preserved; only module and namespace adaptation
-- from assemble_ising_tensor_tractability/IsingTensorTractabilityClosure.lean.
import PlanarHom.BooleanTensorFPSemantics
import PlanarHom.PromisePolynomialTime
import PlanarHom.FixedPowerMachines
import PlanarHom.ListUnaryLengthMachine
import PlanarHom.MixedUnaryParallelMachines
import PlanarHom.FixedFieldEncodingTransport
import PlanarHom.MixedEvaluationFieldMap

/-! Genuine fixed-field FP closure for finitely many tensor factors, an exact
scalar power, and a fixed color equivalence. All endpoints are ordinary raw
planar input problems, using the prescribed basis without a codec assumption. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanTensorFPClosure
open Complexity Complexity.MixedCode
variable {K C D I : Type} [Field K] [Algebra ℚ K]
  [Fintype C] [Fintype D] [Fintype I] [DecidableEq I]
variable {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

theorem fp_product {α : Type} (ea : BitEncoding α) (S : Finset I) (f : α → I → K)
    (hf : ∀ i ∈ S, FP ea (numberFieldEncoding basis) (fun a => f a i)) :
    FP ea (numberFieldEncoding basis) (fun a => ∏ i ∈ S, f a i) := by
  induction S using Finset.induction_on with
  | empty => simpa using fp_const ea (numberFieldEncoding basis) (1 : K)
  | @insert i S hi ih =>
    have ht := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    exact (((hf i (Finset.mem_insert_self _ _)).pair ht).comp
      (FixedFieldArithmetic.fp_multiplication basis)).congr (fun a => by simp [hi])

theorem tensor_inFP (A : I → Matrix C C K)
    (h : ∀ i, (evaluationProblem basis (fun _ : Fin 1 => A i)
      emptyUnaries (fun _ => 1)).InFP) :
    (evaluationProblem basis
      (fun _ : Fin 1 => fun x y : I → C => ∏ i, A i (x i) (y i))
      emptyUnaries (fun _ => 1)).InFP := by
  apply (evaluation_inFP_iff basis _ _ _).mpr
  have hp := fp_product basis (encoding.restrict (PlanarValid 1 0)) Finset.univ
    (fun (g : {g : MixedCode // g.PlanarValid 1 0}) i =>
      g.val.evaluate g.property.1 (fun _ => A i) emptyUnaries (fun _ => 1))
    (fun i _ => (evaluation_inFP_iff basis _ _ _).mp (h i))
  exact hp.congr (fun g => (evaluate_tensor g.val g.property.1 A).symm)

theorem product_inFP (A : Matrix C C K) (B : Matrix D D K)
    (hA : (evaluationProblem basis (fun _ : Fin 1 => A) emptyUnaries (fun _ => 1)).InFP)
    (hB : (evaluationProblem basis (fun _ : Fin 1 => B) emptyUnaries (fun _ => 1)).InFP) :
    (evaluationProblem basis (fun _ : Fin 1 => MultiGraph.tensorInteraction A B)
      emptyUnaries (fun _ => 1)).InFP := by
  apply (evaluation_inFP_iff basis _ _ _).mpr
  exact ((((evaluation_inFP_iff basis _ _ _).mp hA).pair
    ((evaluation_inFP_iff basis _ _ _).mp hB)).comp
      (FixedFieldArithmetic.fp_multiplication basis)).congr
        (fun g => (evaluate_product g.val g.property.1 A B).symm)

theorem scalar_inFP (γ : K) (A : Matrix C C K)
    (hA : (evaluationProblem basis (fun _ : Fin 1 => A) emptyUnaries (fun _ => 1)).InFP) :
    (evaluationProblem basis (fun _ : Fin 1 => γ • A) emptyUnaries (fun _ => 1)).InFP := by
  apply (evaluation_inFP_iff basis _ _ _).mpr
  have hv : FP (encoding.restrict (PlanarValid 1 0)) encoding Subtype.val :=
    fp_code_view _ _ _ (fun _ => rfl)
  have hm := (hv.comp MixedCode.fp_edges).comp
    (ListUnaryLengthMachine.fp_length (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)))
  have hp := hm.comp (FixedPowerMachines.fp_power basis γ)
  exact ((hp.pair ((evaluation_inFP_iff basis _ _ _).mp hA)).comp
    (FixedFieldArithmetic.fp_multiplication basis)).congr
      (fun g => (evaluate_scalar g.val g.property.1 γ A).symm)

theorem color_inFP (e : C ≃ D) (A : Matrix D D K)
    (hA : (evaluationProblem basis (fun _ : Fin 1 => A) emptyUnaries (fun _ => 1)).InFP) :
    (evaluationProblem basis (fun _ : Fin 1 => fun i j => A (e i) (e j))
      emptyUnaries (fun _ => 1)).InFP := by
  apply (evaluation_inFP_iff basis _ _ _).mpr
  apply ((evaluation_inFP_iff basis _ _ _).mp hA).congr
  intro g
  have hu : (fun l i => emptyUnaries l (e i)) = (emptyUnaries : Fin 0 → C → K) := by
    funext l
    exact Fin.elim0 l
  simpa only [hu] using
    (evaluate_color_equiv e g.val g.property.1 (fun _ : Fin 1 => A)
      emptyUnaries (fun _ => 1)).symm

/-- A solver in a genuine finite overfield is converted back by an actual
fixed rational-linear retraction, correct on every source partition value. -/
theorem field_descent_inFP {E : Type} [Field E] [Algebra ℚ E] {e : ℕ}
    (bE : Module.Basis (Fin e) ℚ E) (φ : K →ₐ[ℚ] E) (A : Matrix C C K)
    (hA : (evaluationProblem bE (fun _ : Fin 1 => fun i j => φ (A i j))
      emptyUnaries (fun _ => 1)).InFP) :
    (evaluationProblem basis (fun _ : Fin 1 => A) emptyUnaries (fun _ => 1)).InFP := by
  obtain ⟨back, hback, hfp⟩ := FixedFieldEncodingTransport.exists_fp_leftInverse
    basis bE φ.toLinearMap φ.injective
  apply (evaluation_inFP_iff basis _ _ _).mpr
  apply (((evaluation_inFP_iff bE _ _ _).mp hA).comp hfp).congr
  intro g
  have hu : (fun l i => φ (emptyUnaries l i)) = (emptyUnaries : Fin 0 → C → E) := by
    funext l
    exact Fin.elim0 l
  have hv := map_evaluate φ.toRingHom g.val g.property.1
    (fun _ : Fin 1 => A) emptyUnaries (fun _ => 1)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_one, hu] at hv
  dsimp only [Function.comp_def]
  rw [← hv]
  exact hback _

end PlanarHom.BooleanTensorFPClosure
