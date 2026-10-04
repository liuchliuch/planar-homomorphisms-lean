import PlanarHom.FixedRealTensorCoreEasy
import PlanarHom.FixedRealTwoSideWeights
import PlanarHom.Tensor

/-! A.11 easy direction with two genuinely independent constant side weights.
The target is the literal symmetric bipartite double of c*T(rho), evaluated
in the prescribed fixed real field rather than a finite-Q overfield. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealBipartiteCoreEasy
open DensePolynomial Complexity FixedRealExtension BooleanTensorFPClosure
variable {n e d:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

abbrev Cube (d:ℕ):=Fin d→Bool

def colorEquiv (d:ℕ) : Cube d⊕Cube d ≃ FixedRealTwoSideWeights.Side×Cube d where
  toFun x:=match x with | .inl x=>(.inl 0,x) | .inr x=>(.inr 0,x)
  invFun p:=match p.1 with | .inl _=>.inl p.2 | .inr _=>.inr p.2
  left_inv x:=by cases x <;> rfl
  right_inv p:=by rcases p with ⟨i,x⟩; cases i with
    | inl i=>have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
    | inr i=>have hi:i=0:=Subsingleton.elim _ _; subst i; rfl

def double (γ:K) (ρ:Fin d→K) : Matrix (Cube d⊕Cube d) (Cube d⊕Cube d) K :=
  Matrix.fromBlocks 0 (γ • FixedRealTensorCoreEasy.tensor ρ) (γ • FixedRealTensorCoreEasy.tensor ρ).transpose 0

def weights (α β:K) : Cube d⊕Cube d→K := Sum.elim (fun _=>α) (fun _=>β)

theorem tensor_symmetric (ρ:Fin d→K) (i j:Cube d) :
    FixedRealTensorCoreEasy.tensor ρ i j=FixedRealTensorCoreEasy.tensor ρ j i := by
  apply Finset.prod_congr rfl
  intro k hk
  simp only [BooleanTensorEasyAssembly.isingMatrix,eq_comm]

theorem double_as_product (γ:K) (ρ:Fin d→K) :
    (fun i j=>MultiGraph.tensorInteraction FixedRealTwoSideWeights.interaction
      (γ • FixedRealTensorCoreEasy.tensor ρ) (colorEquiv d i) (colorEquiv d j))=double γ ρ := by
  funext i j
  cases i <;> cases j <;>
    simp [colorEquiv,MultiGraph.tensorInteraction,FixedRealTwoSideWeights.interaction,
      BipartiteRankTwoTractability.matrix,double,tensor_symmetric]

theorem weights_as_product (α β:K) :
    (fun i=>MultiGraph.tensorVertexWeight (FixedRealTwoSideWeights.weights α β) (fun _:Cube d=>1) (colorEquiv d i))=
      weights (d:=d) α β := by
  funext i
  cases i <;> simp only [colorEquiv,Equiv.coe_fn_mk,MultiGraph.tensorVertexWeight,
    FixedRealTwoSideWeights.weights,weights,Sum.elim_inl,Sum.elim_inr,mul_one]

def program (basis:Module.Basis (Fin e) (RationalFunction n) K) (γ α β:K) (ρ:Fin d→K) (g:MixedCode) : Code n e :=
  mul (multiplicationTable basis) (FixedRealTwoSideWeights.program basis α β g)
    (FixedRealTensorCoreEasy.program basis γ 1 ρ g)

theorem fp_program (basis:Module.Basis (Fin e) (RationalFunction n) K) (γ α β:K) (ρ:Fin d→K) :
    FP MixedCode.encoding (encoding n e) (program basis γ α β ρ) :=
  ((FixedRealTwoSideWeights.fp_program basis α β).pair (FixedRealTensorCoreEasy.fp_program basis γ 1 ρ)).comp
    (fp_mul n e (multiplicationTable basis))

theorem program_valid (basis:Module.Basis (Fin e) (RationalFunction n) K) (γ α β:K) (ρ:Fin d→K) (g:MixedCode) :
    Valid n (program basis γ α β ρ g) :=
  mul_valid _ _ _ (FixedRealTwoSideWeights.program_valid basis α β g)
    (FixedRealTensorCoreEasy.program_valid basis γ 1 ρ g)

theorem program_value (basis:Module.Basis (Fin e) (RationalFunction n) K) (f:ℚ→+*K)
    (γ α β:K) (ρ:Fin d→K) (g:MixedCode) (hg:g.PlanarValid 1 0) :
    value basis (program basis γ α β ρ g)=
      g.evaluate hg.1 (fun _:Fin 1=>double γ ρ) emptyUnaries (weights α β) := by
  rw [program,value_mul _ basis (multiplicationTable_realizes basis),
    FixedRealTwoSideWeights.program_value basis α β g hg,
    FixedRealTensorCoreEasy.program_value basis f γ 1 ρ g hg]
  have hc:=MixedCode.evaluate_color_equiv (colorEquiv d) g hg.1
    (fun _:Fin 1=>MultiGraph.tensorInteraction FixedRealTwoSideWeights.interaction (γ • FixedRealTensorCoreEasy.tensor ρ))
    (fun u:Fin 0=>u.elim0) (MultiGraph.tensorVertexWeight (FixedRealTwoSideWeights.weights α β) (fun _:Cube d=>1))
  have hm:(fun (_:Fin 1) i j=>MultiGraph.tensorInteraction FixedRealTwoSideWeights.interaction
      (γ • FixedRealTensorCoreEasy.tensor ρ) (colorEquiv d i) (colorEquiv d j))=fun _:Fin 1=>double γ ρ :=
    funext (fun _=>double_as_product γ ρ)
  have hu:(fun (u:Fin 0) (i:Cube d⊕Cube d)=>
      (u.elim0:FixedRealTwoSideWeights.Side×Cube d→K) (colorEquiv d i))=emptyUnaries := by
    funext u; exact u.elim0
  rw [hm,weights_as_product,hu] at hc
  rw [hc]
  change g.evaluate hg.1 (fun _:Fin 1=>FixedRealTwoSideWeights.interaction) (fun u:Fin 0=>u.elim0)
    (FixedRealTwoSideWeights.weights α β)*
    g.evaluate hg.1 (fun _:Fin 1=>γ • FixedRealTensorCoreEasy.tensor ρ) (fun u:Fin 0=>u.elim0) (fun _=>1)=_
  rw [MixedCode.evaluate_homogeneous,MixedCode.evaluate_homogeneous,MixedCode.evaluate_homogeneous]
  exact ((g.toMultiGraph hg.1).partition_tensor _ _ _ _).symm

def problem (basis:Module.Basis (Fin e) (RationalFunction n) K) (γ α β:K) (ρ:Fin d→K) : RepresentedBit.Problem :=
  (presentation basis).problem MixedCode.encoding (MixedCode.PlanarValid 1 0)
    (MixedCode.totalEvaluation (fun _:Fin 1=>double γ ρ) emptyUnaries (weights α β))

theorem inFP (basis:Module.Basis (Fin e) (RationalFunction n) K) (f:ℚ→+*K)
    (γ α β:K) (ρ:Fin d→K) : (problem basis γ α β ρ).InFP := by
  apply RepresentedBit.Presentation.problem_inFP _ _ MixedCode.normalizer _ _
    (program basis γ α β ρ) (fp_program basis γ α β ρ) (fun g _=>program_valid basis γ α β ρ g)
  intro g hg
  rw [MixedCode.totalEvaluation_valid _ _ _ g hg.1]
  exact program_value basis f γ α β ρ g hg

end PlanarHom.FixedRealBipartiteCoreEasy
