import PlanarHom.FixedRealIsingInterpolation
import PlanarHom.FixedRealListProductCorrectness
import PlanarHom.BooleanTensorFPSemantics

/-! Actual fixed-real evaluation of scalar Ising tensors with a constant
vertex weight. The original prescribed RF-basis presentation is preserved. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealTensorCoreEasy
open DensePolynomial Complexity PairProjectionMachines BooleanTensorFPClosure
variable {n e d:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

def tensor (ρ:Fin d→K) : Matrix (Fin d→Bool) (Fin d→Bool) K :=
  fun i j=>∏k,BooleanTensorEasyAssembly.isingMatrix (ρ k) (i k) (j k)

def tensorProgram (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:Fin d→K) (g:MixedCode) :
    FixedRealExtension.Code n e :=
  FixedRealListProduct.product basis (List.ofFn (fun k=>FixedRealIsingInterpolation.program basis (ρ k) g))

theorem fp_tensorProgram (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:Fin d→K) :
    FP MixedCode.encoding (FixedRealExtension.encoding n e) (tensorProgram basis ρ) := by
  have hv:FP MixedCode.encoding ((FixedRealExtension.encoding n e).vector d)
      (fun g k=>FixedRealIsingInterpolation.program basis (ρ k) g) :=
    FixedVectorMachines.fp_assemble _ _ _ _ (fun k=>FixedRealIsingInterpolation.fp_program basis (ρ k))
  have hl:FP MixedCode.encoding (FixedRealExtension.encoding n e).list
      (fun g=>List.ofFn (fun k=>FixedRealIsingInterpolation.program basis (ρ k) g)) := hv.transportOutput (fun _=>rfl)
  exact hl.comp (FixedRealListProduct.fp_product basis)

theorem tensorProgram_valid (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:Fin d→K) (g:MixedCode) :
    FixedRealExtension.Valid n (tensorProgram basis ρ g) := by
  apply FixedRealListProduct.product_valid
  intro a ha
  obtain ⟨k,rfl⟩:=List.mem_ofFn.mp ha
  exact FixedRealIsingInterpolation.program_valid basis (ρ k) g

theorem tensorProgram_value (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (f:ℚ→+*K) (ρ:Fin d→K) (g:MixedCode) (hg:g.PlanarValid 1 0) :
    FixedRealExtension.value basis (tensorProgram basis ρ g)=
      g.evaluate hg.1 (fun _:Fin 1=>tensor ρ) emptyUnaries (fun _=>1) := by
  rw [tensorProgram,FixedRealListProduct.product_value]
  · simp only [List.map_ofFn,List.prod_ofFn,Function.comp_def,
      FixedRealIsingInterpolation.program_value basis f _ g hg]
    change (∏k,(g.toMultiGraph hg.1).partition (BooleanTensorEasyAssembly.isingMatrix (ρ k)) (fun _=>1))=
      g.evaluate hg.1 (fun _:Fin 1=>fun x y:Fin d→Bool=>∏k,BooleanTensorEasyAssembly.isingMatrix (ρ k) (x k) (y k)) emptyUnaries (fun _=>1)
    rw [evaluate_tensor]
    apply Finset.prod_congr rfl
    intro k hk
    exact (MixedCode.evaluate_homogeneous g hg.1 _ _).symm
  · intro a ha
    obtain ⟨k,rfl⟩:=List.mem_ofFn.mp ha
    exact FixedRealIsingInterpolation.program_valid basis (ρ k) g

def program (basis:Module.Basis (Fin e) (RationalFunction n) K) (γ u:K) (ρ:Fin d→K) (g:MixedCode) :
    FixedRealExtension.Code n e :=
  FixedRealExtension.mul (FixedRealExtension.multiplicationTable basis)
    (FixedRealCoefficientEvaluation.power basis u g.vertices)
    (FixedRealExtension.mul (FixedRealExtension.multiplicationTable basis)
      (FixedRealCoefficientEvaluation.power basis γ g.edges.length) (tensorProgram basis ρ g))

theorem fp_program (basis:Module.Basis (Fin e) (RationalFunction n) K) (γ u:K) (ρ:Fin d→K) :
    FP MixedCode.encoding (FixedRealExtension.encoding n e) (program basis γ u ρ) := by
  have hu:=MixedCode.fp_vertices.comp (FixedRealCoefficientEvaluation.fp_power basis u)
  have he:=MixedCode.fp_edges.comp (ListUnaryLengthMachine.fp_length (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)))
  have hγ:=he.comp (FixedRealCoefficientEvaluation.fp_power basis γ)
  have hm:=FixedRealExtension.fp_mul n e (FixedRealExtension.multiplicationTable basis)
  exact (hu.pair ((hγ.pair (fp_tensorProgram basis ρ)).comp hm)).comp hm

theorem program_valid (basis:Module.Basis (Fin e) (RationalFunction n) K) (γ u:K) (ρ:Fin d→K) (g:MixedCode) :
    FixedRealExtension.Valid n (program basis γ u ρ g) :=
  FixedRealExtension.mul_valid _ _ _ (FixedRealCoefficientEvaluation.power_valid basis u _) <|
    FixedRealExtension.mul_valid _ _ _ (FixedRealCoefficientEvaluation.power_valid basis γ _)
      (tensorProgram_valid basis ρ g)

theorem evaluate_constant_weights {C:Type} [Fintype C] (g:MixedCode) (hg:g.Valid 1 0)
    (M:Matrix C C K) (u:K) :
    g.evaluate hg (fun _:Fin 1=>M) emptyUnaries (fun _=>u)=
      u^g.vertices*g.evaluate hg (fun _:Fin 1=>M) emptyUnaries (fun _=>1) := by
  change g.evaluate hg (fun _:Fin 1=>M) (fun a:Fin 0=>a.elim0) (fun _=>u)=
    u^g.vertices*g.evaluate hg (fun _:Fin 1=>M) (fun a:Fin 0=>a.elim0) (fun _=>1)
  rw [MixedCode.evaluate_homogeneous,MixedCode.evaluate_homogeneous]
  simp only [MultiGraph.partition,MultiGraph.assignmentWeight,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,one_pow,one_mul,Finset.mul_sum]

theorem program_value (basis:Module.Basis (Fin e) (RationalFunction n) K) (f:ℚ→+*K)
    (γ u:K) (ρ:Fin d→K) (g:MixedCode) (hg:g.PlanarValid 1 0) :
    FixedRealExtension.value basis (program basis γ u ρ g)=
      g.evaluate hg.1 (fun _:Fin 1=>γ • tensor ρ) emptyUnaries (fun _=>u) := by
  rw [program,FixedRealExtension.value_mul _ basis (FixedRealExtension.multiplicationTable_realizes basis),
    FixedRealExtension.value_mul _ basis (FixedRealExtension.multiplicationTable_realizes basis),
    FixedRealCoefficientEvaluation.power_value,FixedRealCoefficientEvaluation.power_value,
    tensorProgram_value basis f ρ g hg]
  rw [evaluate_constant_weights g hg.1 (γ • tensor ρ) u,evaluate_scalar]

def problem (basis:Module.Basis (Fin e) (RationalFunction n) K) (γ u:K) (ρ:Fin d→K) : RepresentedBit.Problem :=
  (FixedRealExtension.presentation basis).problem MixedCode.encoding (MixedCode.PlanarValid 1 0)
    (MixedCode.totalEvaluation (fun _:Fin 1=>γ • tensor ρ) emptyUnaries (fun _=>u))

theorem inFP (basis:Module.Basis (Fin e) (RationalFunction n) K) (f:ℚ→+*K)
    (γ u:K) (ρ:Fin d→K) : (problem basis γ u ρ).InFP := by
  apply RepresentedBit.Presentation.problem_inFP _ _ MixedCode.normalizer _ _
    (program basis γ u ρ) (fp_program basis γ u ρ) (fun g _=>program_valid basis γ u ρ g)
  intro g hg
  rw [MixedCode.totalEvaluation_valid _ _ _ g hg.1]
  exact program_value basis f γ u ρ g hg

end PlanarHom.FixedRealTensorCoreEasy
