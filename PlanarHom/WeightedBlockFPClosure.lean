import PlanarHom.TractableBlockComposition

/-! NEW weighted finite-product, color and fixed-field descent programs.
Every vertex weight is preserved in the literal tensor/color semantics. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.WeightedBlockTractability
open Complexity Complexity.MixedCode BooleanTensorFPClosure
variable {C D K : Type} [Fintype C] [Fintype D] [Field K] [Algebra ℚ K]
variable {dimension : ℕ}

theorem color_inFP (basis : Module.Basis (Fin dimension) ℚ K) (e : C ≃ D)
    (M : Matrix D D K) (w : D → K)
    (h : (evaluationProblem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w).InFP) :
    (evaluationProblem basis (fun _:Fin 1=>fun i j=>M (e i) (e j))
      (fun u:Fin 0=>u.elim0) (fun i=>w (e i))).InFP := by
  apply (evaluation_inFP_iff basis _ _ _).mpr
  apply ((evaluation_inFP_iff basis _ _ _).mp h).congr
  intro g
  have hu : (fun (u:Fin 0) (i:C)=>(u.elim0:D→K) (e i))=(fun u:Fin 0=>u.elim0) := by
    funext u
    exact u.elim0
  simpa only [hu] using (evaluate_color_equiv e g.val g.property.1
    (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w).symm

theorem field_descent_inFP (basis : Module.Basis (Fin dimension) ℚ K)
    {E : Type} [Field E] [Algebra ℚ E] {n : ℕ} (bE : Module.Basis (Fin n) ℚ E)
    (φ : K →ₐ[ℚ] E) (M : Matrix C C K) (w : C → K)
    (h : (evaluationProblem bE (fun _:Fin 1=>fun i j=>φ (M i j))
      (fun u:Fin 0=>u.elim0) (fun i=>φ (w i))).InFP) :
    (evaluationProblem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w).InFP := by
  obtain ⟨back,hback,hfp⟩ := FixedFieldEncodingTransport.exists_fp_leftInverse
    basis bE φ.toLinearMap φ.injective
  apply (evaluation_inFP_iff basis _ _ _).mpr
  apply (((evaluation_inFP_iff bE _ _ _).mp h).comp hfp).congr
  intro g
  have hu : (fun (u:Fin 0) (i:C)=>φ ((u.elim0:C→K) i))=(fun u:Fin 0=>u.elim0) := by
    funext u
    exact u.elim0
  have he := map_evaluate φ.toRingHom g.val g.property.1
    (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w
  simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,hu] at he
  dsimp only [Function.comp_def]
  rw [←he]
  exact hback _

theorem product_inFP (basis : Module.Basis (Fin dimension) ℚ K)
    (A : Matrix C C K) (B : Matrix D D K) (μ : C → K) (ν : D → K)
    (hA : (evaluationProblem basis (fun _:Fin 1=>A) (fun u:Fin 0=>u.elim0) μ).InFP)
    (hB : (evaluationProblem basis (fun _:Fin 1=>B) (fun u:Fin 0=>u.elim0) ν).InFP) :
    (evaluationProblem basis (fun _:Fin 1=>MultiGraph.tensorInteraction A B)
      (fun u:Fin 0=>u.elim0) (MultiGraph.tensorVertexWeight μ ν)).InFP := by
  apply (evaluation_inFP_iff basis _ _ _).mpr
  have hprod := (((evaluation_inFP_iff basis _ _ _).mp hA).pair
    ((evaluation_inFP_iff basis _ _ _).mp hB)).comp (FixedFieldArithmetic.fp_multiplication basis)
  apply hprod.congr
  intro g
  simp only [evaluate_homogeneous]
  exact ((g.val.toMultiGraph g.property.1).partition_tensor A B μ ν).symm

end PlanarHom.WeightedBlockTractability
