import PlanarHom.SurfaceRowEvaluation
import PlanarHom.WeightedBlockFPClosure

/-! NEW exact supplied-row closures. Tensor, color, scalar and field changes
preserve the literal graph and row data; vertex weights remain explicit. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceWeightedBlockTractability
open Complexity Complexity.MixedCode SurfaceRowEvaluation BooleanTensorFPClosure
variable {ambient:ℕ} {C D I K:Type} [Fintype C] [Fintype D] [Fintype I] [DecidableEq I]
variable [Field K] [Algebra ℚ K] {dimension:ℕ}

theorem color_inFP (basis:Module.Basis (Fin dimension) ℚ K) (e:C≃D)
    (M:Matrix D D K) (w:D→K)
    (h:Evaluable ambient basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w) :
    Evaluable ambient basis (fun _:Fin 1=>fun i j=>M (e i) (e j))
      (fun u:Fin 0=>u.elim0) (fun i=>w (e i)) := by
  apply h.congr
  intro p
  have hu:(fun (u:Fin 0) (i:C)=>(u.elim0:D→K) (e i))=(fun u:Fin 0=>u.elim0):=by
    funext u
    exact u.elim0
  simpa only [hu] using (evaluate_color_equiv e p.val.1 (graph_valid p.property)
    (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w).symm

theorem field_descent_inFP (basis:Module.Basis (Fin dimension) ℚ K)
    {E:Type} [Field E] [Algebra ℚ E] {n:ℕ} (bE:Module.Basis (Fin n) ℚ E)
    (φ:K→ₐ[ℚ]E) (M:Matrix C C K) (w:C→K)
    (h:Evaluable ambient bE (fun _:Fin 1=>fun i j=>φ (M i j))
      (fun u:Fin 0=>u.elim0) (fun i=>φ (w i))) :
    Evaluable ambient basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w := by
  obtain ⟨back,hback,hfp⟩:=FixedFieldEncodingTransport.exists_fp_leftInverse basis bE φ.toLinearMap φ.injective
  apply (h.comp hfp).congr
  intro p
  have hu:(fun (u:Fin 0) (i:C)=>φ ((u.elim0:C→K) i))=(fun u:Fin 0=>u.elim0):=by
    funext u
    exact u.elim0
  have he:=map_evaluate φ.toRingHom p.val.1 (graph_valid p.property)
    (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w
  simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,hu] at he
  dsimp only [Function.comp_def]
  rw [←he]
  exact hback _

theorem product_inFP (basis:Module.Basis (Fin dimension) ℚ K)
    (A:Matrix C C K) (B:Matrix D D K) (μ:C→K) (ν:D→K)
    (hA:Evaluable ambient basis (fun _:Fin 1=>A) (fun u:Fin 0=>u.elim0) μ)
    (hB:Evaluable ambient basis (fun _:Fin 1=>B) (fun u:Fin 0=>u.elim0) ν) :
    Evaluable ambient basis (fun _:Fin 1=>MultiGraph.tensorInteraction A B)
      (fun u:Fin 0=>u.elim0) (MultiGraph.tensorVertexWeight μ ν) := by
  apply ((hA.pair hB).comp (FixedFieldArithmetic.fp_multiplication basis)).congr
  intro p
  simp only [evaluate_homogeneous]
  exact ((p.val.1.toMultiGraph (graph_valid p.property)).partition_tensor A B μ ν).symm

theorem tensor_inFP (basis:Module.Basis (Fin dimension) ℚ K) (A:I→Matrix C C K)
    (h:∀i,Evaluable ambient basis (fun _:Fin 1=>A i) emptyUnaries (fun _=>1)) :
    Evaluable ambient basis (fun _:Fin 1=>fun x y:I→C=>∏i,A i (x i) (y i)) emptyUnaries (fun _=>1) := by
  have hp:=BooleanTensorFPClosure.fp_product basis
    (SurfaceRowEvaluation.encoding.restrict (SurfaceRowEvaluation.Valid 1 0 ambient)) Finset.univ
    (fun (p:{p:SurfaceRowEvaluation.Input // SurfaceRowEvaluation.Valid 1 0 ambient p}) i=>
      p.val.1.evaluate (graph_valid p.property) (fun _=>A i) emptyUnaries (fun _=>1)) (fun i _=>h i)
  exact hp.congr (fun p=>(BooleanTensorFPClosure.evaluate_tensor p.val.1 (graph_valid p.property) A).symm)

theorem scalar_inFP (basis:Module.Basis (Fin dimension) ℚ K) (γ:K) (A:Matrix C C K)
    (h:Evaluable ambient basis (fun _:Fin 1=>A) emptyUnaries (fun _=>1)) :
    Evaluable ambient basis (fun _:Fin 1=>γ • A) emptyUnaries (fun _=>1) := by
  have hm:=((fp_graph (b:=1) (u:=0) ambient).comp MixedCode.fp_edges).comp
    (ListUnaryLengthMachine.fp_length (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)))
  have hp:=hm.comp (FixedPowerMachines.fp_power basis γ)
  exact ((hp.pair h).comp (FixedFieldArithmetic.fp_multiplication basis)).congr
    (fun p=>(BooleanTensorFPClosure.evaluate_scalar p.val.1 (graph_valid p.property) γ A).symm)

theorem rankOne_inFP {q:ℕ} (basis:Module.Basis (Fin dimension) ℚ K) (a w:Fin q→K) :
    Evaluable ambient basis (fun _:Fin 1=>fun i j=>a i*a j) (fun u:Fin 0=>u.elim0) w := by
  exact ((fp_graph ambient).comp (RankOneEvaluationMachine.fp_evaluate basis a w)).congr
    (fun p=>(GraphDegreeMachines.rankOne_evaluate p.val.1 (graph_valid p.property) a w).symm)

end PlanarHom.SurfaceWeightedBlockTractability
