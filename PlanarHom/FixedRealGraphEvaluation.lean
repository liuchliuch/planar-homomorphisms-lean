import PlanarHom.FixedRealEvaluationPrograms
import PlanarHom.FixedRealIsingInterpolation
import PlanarHom.FixedRealComponentReduction
import PlanarHom.TractableBlockComposition

/-! NEW concrete represented homogeneous graph evaluators and their exact
weighted color, product, tensor, scalar and component closure. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealGraphEvaluation
open Complexity Complexity.MixedCode DensePolynomial FixedRealEvaluation BooleanTensorFPClosure
variable {n e:ℕ} {K C D I B:Type} [Field K] [Algebra (RationalFunction n) K]
variable [Fintype C] [Fintype D] [Fintype I] [Fintype B]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def value (M:Matrix C C K) (w:C→K) : MixedCode→K :=
  totalEvaluation (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w
abbrev Computer (M:Matrix C C K) (w:C→K) :=
  Program basis MixedCode.encoding (PlanarValid 1 0) (value M w)
def Evaluable (M:Matrix C C K) (w:C→K) : Prop:=Nonempty (Computer basis M w)
abbrev ConnectedComputer (M:Matrix C C K) (w:C→K) :=
  Program basis MixedCode.encoding (FixedRealComponents.connectedValid (b:=1) (u:=0)) (value M w)

 theorem inFP (M:Matrix C C K) (w:C→K) (h:Evaluable basis M w) :
    (FixedRealComponents.problem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w).InFP := by
  obtain ⟨P⟩:=h
  exact P.inFP MixedCode.normalizer

 theorem ising (f:ℚ→+*K) (ρ:K) : Evaluable basis (BooleanTensorEasyAssembly.isingMatrix ρ) (fun _=>1) := by
  refine ⟨⟨FixedRealIsingInterpolation.program basis ρ,FixedRealIsingInterpolation.fp_program basis ρ,
    fun g _=>FixedRealIsingInterpolation.program_valid basis ρ g,?_⟩⟩
  intro g hp
  rw [value,totalEvaluation_valid _ _ _ g hp.1,evaluate_homogeneous]
  exact FixedRealIsingInterpolation.program_value basis f ρ g hp

 theorem color (i:C≃D) (M:Matrix D D K) (w:D→K) (h:Evaluable basis M w) :
    Evaluable basis (fun a b=>M (i a) (i b)) (fun a=>w (i a)) := by
  obtain ⟨P⟩:=h
  refine ⟨P.congr _ ?_⟩
  intro g hp
  simp only [value,totalEvaluation_valid _ _ _ g hp.1]
  have hu:(fun (u:Fin 0) (a:C)=>(u.elim0:D→K) (i a))=(fun u:Fin 0=>u.elim0):=by funext u;exact u.elim0
  simpa only [hu] using (evaluate_color_equiv i g hp.1 (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w).symm

 theorem product (A:Matrix C C K) (B:Matrix D D K) (μ:C→K) (ν:D→K)
    (hA:Evaluable basis A μ) (hB:Evaluable basis B ν) :
    Evaluable basis (MultiGraph.tensorInteraction A B) (MultiGraph.tensorVertexWeight μ ν) := by
  obtain ⟨P⟩:=hA
  obtain ⟨Q⟩:=hB
  refine ⟨(P.mul Q).congr _ ?_⟩
  intro g hp
  simp only [value,totalEvaluation_valid _ _ _ g hp.1,evaluate_homogeneous]
  exact ((g.toMultiGraph hp.1).partition_tensor A B μ ν).symm

 def power (ρ:K) : Program basis BitEncoding.unaryNat (fun _=>True) (fun d=>ρ^d) where
  run:=FixedRealCoefficientEvaluation.power basis ρ
  fp:=FixedRealCoefficientEvaluation.fp_power basis ρ
  valid d _:=FixedRealCoefficientEvaluation.power_valid basis ρ d
  value d _:=FixedRealCoefficientEvaluation.power_value basis ρ d

 theorem scalar (γ:K) (A:Matrix C C K) (h:Evaluable basis A (fun _=>1)) :
    Evaluable basis (γ • A) (fun _=>1) := by
  obtain ⟨P⟩:=h
  have hd:=MixedCode.fp_edges.comp (ListUnaryLengthMachine.fp_length
    (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)))
  let Q:Program basis MixedCode.encoding (PlanarValid 1 0) (fun g=>γ^g.edges.length):=
    (power basis γ).pullback _ _ (fun g:MixedCode=>g.edges.length) hd (fun _ _=>True.intro)
  refine ⟨(Q.mul P).congr _ ?_⟩
  intro g hp
  simp only [value,totalEvaluation_valid _ _ _ g hp.1]
  exact (evaluate_scalar g hp.1 γ A).symm

 theorem tensor [DecidableEq I] (A:I→Matrix C C K) (h:∀i,Evaluable basis (A i) (fun _=>1)) :
    Evaluable basis (fun x y:I→C=>∏i,A i (x i) (y i)) (fun _=>1) := by
  let P:∀i,Computer basis (A i) (fun _=>1):=fun i=>Classical.choice (h i)
  refine ⟨(Program.prod Finset.univ (fun i=>value (A i) (fun _=>1)) P).congr _ ?_⟩
  intro g hp
  simp only [value,totalEvaluation_valid _ _ _ g hp.1]
  exact (evaluate_tensor g hp.1 A).symm

 theorem components (M:Matrix C C K) (w:C→K) (P:ConnectedComputer basis M w) :
    Evaluable basis M w := by
  let Q:Computer basis M w:=(P.productMap.pullback MixedCode.encoding (PlanarValid 1 0)
    GraphComponentCode.components GraphComponentMachines.fp_components
    (fun g hp=>GraphComponentCode.components_promises g hp)).congr _ (by
      intro g hp
      rw [value,totalEvaluation_valid _ _ _ g hp.1,GraphComponentCode.evaluate_components g hp.1])
  exact ⟨Q⟩

 theorem fibers (block:C→B) (M:Matrix C C K) (hs:∀i j,M i j=M j i)
    (hz:∀i j,block i≠block j→M i j=0) (w:C→K)
    (h:∀b,Evaluable basis (fun i j:{i // block i=b}=>M i.val j.val) (fun i=>w i.val)) :
    Evaluable basis M w := by
  let P:∀b,ConnectedComputer basis (fun i j:{i // block i=b}=>M i.val j.val) (fun i=>w i.val):=
    fun b=>(Classical.choice (h b)).pullback _ _ id (fp_id MixedCode.encoding) (fun _ hp=>hp.1)
  apply components basis M w
  refine (Program.sum Finset.univ (fun b=>value (fun i j:{i // block i=b}=>M i.val j.val)
    (fun i=>w i.val)) P).congr _ ?_
  intro g hp
  simp only [value,totalEvaluation_valid _ _ _ g hp.1.1]
  letI:Algebra ℚ K:=((algebraMap (RationalFunction n) K).comp
    ((algebraMap (Poly n) (RationalFunction n)).comp (DensePolynomial.qHom n))).toAlgebra
  exact (TractableBlockComposition.evaluate_eq_sum_fibers g hp.1.1 hp.2.1 hp.2.2 M hs block hz w).symm

 theorem rankOne {q:ℕ} (a w:Fin q→K) : Evaluable basis (fun i j=>a i*a j) w := by
  let P:Program basis BitEncoding.unaryNat (fun _=>True) (fun d=>∑i:Fin q,w i*a i^d):=
    Program.sum Finset.univ (fun i d=>w i*a i^d) (fun i=>(Program.constant basis _ _ (w i)).mul (power basis (a i)))
  refine ⟨(P.productMap.pullback MixedCode.encoding (PlanarValid 1 0)
    GraphDegreeMachines.degrees GraphDegreeMachines.fp_degrees (fun _ _ _ _=>True.intro)).congr _ ?_⟩
  intro g hp
  rw [value,totalEvaluation_valid _ _ _ g hp.1]
  exact (GraphDegreeMachines.rankOne_evaluate g hp.1 a w).symm

end PlanarHom.FixedRealGraphEvaluation
