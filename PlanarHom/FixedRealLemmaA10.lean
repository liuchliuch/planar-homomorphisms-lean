import PlanarHom.FixedRealTensorCoreEasy
import PlanarHom.FixedRealSymmetricCoreHard
import PlanarHom.FixedRealColorReduction

/-! Lemma A.10 for the literal nondegenerate positive Ising tensor. Both the
tractable and hard directions use the original prescribed real-field output. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealLemmaA10
open DensePolynomial Complexity FixedRealExtension RepresentedBit FixedRealMixedInterpolation
open RelativeWeightedSpectralField Boolean
variable {n e d q:ℕ} {F:Type} [Field F] [Algebra (RationalFunction n) F] [Algebra F ℝ]

 theorem tensor_real (ρ:Fin d→F) (i j:Cube d) :
    algebraMap F ℝ (FixedRealTensorCoreEasy.tensor ρ i j)=Boolean.tensor (fun k=>algebraMap F ℝ (ρ k)) i j := by
  simp only [FixedRealTensorCoreEasy.tensor,Boolean.tensor,map_prod,BooleanTensorEasyAssembly.isingMatrix,
    Boolean.W,apply_ite,map_one]

 def problem (basis:Module.Basis (Fin e) (RationalFunction n) F) (ρ:Fin d→F) (u:Cube d→F) : Problem :=
  FixedRealComponents.problem basis (fun _:Fin 1=>FixedRealTensorCoreEasy.tensor ρ)
    (fun l:Fin 0=>l.elim0) u

 theorem constant_inFP (basis:Module.Basis (Fin e) (RationalFunction n) F) (ρ:Fin d→F)
    (u:Cube d→F) (hconst:∀i j,u i=u j) : (problem basis ρ u).InFP := by
  let c:=u (fun _=>false)
  let f:ℚ→+*F:=(algebraMap (RationalFunction n) F).comp
    ((algebraMap (Poly n) (RationalFunction n)).comp (qHom n))
  have hw:u=(fun _=>c):=funext (fun i=>hconst i _)
  have hh:=FixedRealTensorCoreEasy.inFP basis f 1 c ρ
  have hu:(BooleanTensorFPClosure.emptyUnaries:Fin 0→Cube d→F)=(fun l:Fin 0=>l.elim0) := by
    funext l; exact l.elim0
  simpa only [problem,FixedRealComponents.problem,FixedRealTensorCoreEasy.problem,one_smul,hu,hw] using hh

 theorem tensor_nonconstant_hard (basis:Module.Basis (Fin e) (RationalFunction n) F) (ρ:Fin d→F)
    (hρ:∀j,0<algebraMap F ℝ (ρ j)) (hne:∀j,algebraMap F ℝ (ρ j)≠1)
    (u:Cube d→F) (hu:∀i,0<algebraMap F ℝ (u i)) (hnon:∃i j,u i≠u j) :
    SharpPHard (problem basis ρ u) := by
  let order:Fin (Fintype.card (Cube d))≃Cube d:=(Fintype.equivFin _).symm
  let M:Matrix (Fin (Fintype.card (Cube d))) (Fin (Fintype.card (Cube d))) F :=
    fun i j=>FixedRealTensorCoreEasy.tensor ρ (order i) (order j)
  let w:=fun i=>u (order i)
  let ρR:=fun j=>algebraMap F ℝ (ρ j)
  have he:realMatrix M=Matrix.reindex order.symm order.symm (Matrix.of (Boolean.tensor ρR)) := by
    ext i j
    exact tensor_real ρ (order i) (order j)
  have hsym:∀i j,realMatrix M i j=realMatrix M j i := by
    intro i j
    change algebraMap F ℝ (FixedRealTensorCoreEasy.tensor ρ (order i) (order j))=
      algebraMap F ℝ (FixedRealTensorCoreEasy.tensor ρ (order j) (order i))
    rw [tensor_real,tensor_real]
    exact Boolean.tensor_symm _ _ _
  have hunit:IsUnit (realMatrix M) := by
    rw [he,Matrix.isUnit_iff_isUnit_det,Matrix.det_reindex_self]
    exact (Matrix.isUnit_iff_isUnit_det _).mp ((tensor_isUnit_iff_of_pos hρ).mpr hne)
  have hpos:∀i j,0<realMatrix M i j := by
    intro i j
    change 0<algebraMap F ℝ (FixedRealTensorCoreEasy.tensor ρ (order i) (order j))
    rw [tensor_real]
    exact tensor_pos hρ _ _
  have hrow:∀i,∑j,(realMatrix M i j)^2=∏k,(1+(ρR k)^2) := by
    intro i
    change (∑j,(algebraMap F ℝ (FixedRealTensorCoreEasy.tensor ρ (order i) (order j)))^2)=_
    simp only [tensor_real]
    rw [order.sum_comp (fun j=>(Boolean.tensor ρR (order i) j)^2)]
    simp_rw [←Boolean.tensor_pow]
    exact Boolean.tensor_row_sum _ _
  have hnon':∃i j,w i≠w j := by
    obtain ⟨i,j,hij⟩:=hnon
    exact ⟨order.symm i,order.symm j,by simpa only [w,Equiv.apply_symm_apply] using hij⟩
  have hard:=FixedRealSymmetricCoreHard.nonconstant_weights_hard basis M w hsym hunit hpos _ hrow
    (fun i=>hu (order i)) hnon'
  exact hard.trans (FixedRealColorReduction.homogeneous basis order (FixedRealTensorCoreEasy.tensor ρ) u)

/-- Full exact A.10, with numerical hypotheses only. -/
theorem lemmaA10 (basis:Module.Basis (Fin e) (RationalFunction n) F) (ρ:Fin d→F)
    (hρ:∀j,0<algebraMap F ℝ (ρ j)) (hne:∀j,algebraMap F ℝ (ρ j)≠1)
    (u:Cube d→F) (hu:∀i,0<algebraMap F ℝ (u i)) :
    ((∀i j,u i=u j)→(problem basis ρ u).InFP) ∧
      ((∃i j,u i≠u j)→SharpPHard (problem basis ρ u)) :=
  ⟨constant_inFP basis ρ u,tensor_nonconstant_hard basis ρ hρ hne u hu⟩

end PlanarHom.FixedRealLemmaA10
