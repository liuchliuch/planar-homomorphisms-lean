import PlanarHom.BooleanNormalizedRetention
import PlanarHom.BooleanRetainedRootReduction
import PlanarHom.HammingPottsToSource

/-! NEW end-to-end reduction from an actual positive biased Boolean factor to
the original normalized tensor source. The source compiler, interpolation and
positive-root extraction are all constructed. -/
noncomputable section
open Classical
namespace PlanarHom.BooleanBiasedFactorReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases BooleanTensorSpectral
open BooleanNormalizedRetention BooleanRetentionReduction BooleanSpectralCounts BooleanPDNormalization
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {b d q bt ut dimension : ℕ}

def factor (θ w : K) (k : ℕ) : Matrix Bool Bool K :=
  block (cValue θ (2*k+1)) (aValue θ (2*k+1)) (w*(1/2))

theorem factor_real (θ w : K) (k : ℕ) :
    (factor θ w k).map K.val.toRingHom=normalForm ((θ:ℝ)^(2*k+1)) ((w:ℝ)*(1/2)) := by
  change (factor θ w k).map K.val.toRingHom=_
  rw [factor,BooleanTensorRingMap.block_map]
  simp only [map_mul,map_div₀,map_one,map_ofNat]
  change block (cValue θ (2*k+1):ℝ) (aValue θ (2*k+1):ℝ) ((w:ℝ)*(1/2))=_
  rw [cValue_real,aValue_real,block_eq_normalForm]

theorem factor_properties (θ w : K) (hθ:1<(θ:ℝ)) (hw:0<(w:ℝ)) (hw1:(w:ℝ)<1) (k : ℕ) :
    (∀i j,factor θ w k i j=factor θ w k j i) ∧
    (∀i j,0<(factor θ w k i j:ℝ)) ∧
    factor θ w k false false≠factor θ w k true true ∧
    factor θ w k false false*factor θ w k true true≠factor θ w k false true^2 := by
  have ht:1<(θ:ℝ)^(2*k+1):=one_lt_pow₀ hθ (by omega)
  have ht0:0<(θ:ℝ)^(2*k+1):=lt_trans zero_lt_one ht
  have he (i j:Bool):(factor θ w k i j:ℝ)=normalForm ((θ:ℝ)^(2*k+1)) ((w:ℝ)*(1/2)) i j:=
    congrFun (congrFun (factor_real θ w k) i) j
  refine ⟨?_,?_,?_,?_⟩
  · intro i j
    apply Subtype.ext
    rw [he,he]
    cases i <;> cases j <;> rfl
  · intro i j
    rw [he]
    cases i <;> cases j <;> simp only [normalForm,ite_true,ite_false,Bool.false_eq_true,Bool.true_eq_false]
    · exact ht0
    · positivity
    · positivity
    · exact inv_pos.mpr ht0
  · intro hz
    have hz':(factor θ w k false false:ℝ)=(factor θ w k true true:ℝ):=congrArg Subtype.val hz
    rw [he,he] at hz'
    simp only [normalForm,ite_true,Bool.false_eq_true,ite_false] at hz'
    have hi:=inv_lt_one_of_one_lt₀ ht
    linarith
  · intro hz
    have hz':(factor θ w k false false:ℝ)*(factor θ w k true true:ℝ)=
        (factor θ w k false true:ℝ)^2:=by
      simpa only [map_mul,map_pow] using congrArg K.val.toRingHom hz
    rw [he,he,he] at hz'
    simp only [normalForm,ite_true,Bool.false_eq_true,ite_false,mul_inv_cancel₀ ht0.ne'] at hz'
    nlinarith

theorem exists_biased_factor (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (old : Fin bt)
    (e : Fin q≃(Fin d→Bool)) (γ : K) (hγ:0<(γ:ℝ))
    (cls : Fin d→Fin b) (θ w : Fin b→K)
    (hθ:∀i,1≤(θ i:ℝ)) (hw:∀i,0<(w i:ℝ)) (hw1:∀i,(w i:ℝ)<1)
    (hrep:Function.Injective (fun i=>((θ i:ℝ),(w i:ℝ))))
    (hsource:Matrix.reindex e e (SpectralFieldPresentation.realMatrix (M old))=
      (γ:ℝ) • CubeTensorExponential.tensor
        (fun r=>normalForm (θ (cls r):ℝ) (w (cls r):ℝ)))
    (g0 : Fin b) (hg0:1<(θ g0:ℝ)) (hoccurs:∃r,cls r=g0) :
    ∃B:Matrix Bool Bool K,(∀i j,B i j=B j i) ∧ (∀i j,0<(B i j:ℝ)) ∧
      B false false≠B true true ∧ B false false*B true true≠B false true^2 ∧
      Nonempty (PromisePolyTimeTuringReduction
        (evaluationProblem basis (fun _:Fin 1=>B) (fun u:Fin 0=>u.elim0) (fun _=>1))
        (evaluationProblem basis M U (fun _=>1))) := by
  obtain ⟨k,⟨retention⟩⟩:=exists_retained_reduction basis M U old e γ hγ cls θ w hθ hw hw1 hrep hsource g0 hg0 (1/2)
  let S:=Finset.univ.filter (fun r=>cls r=g0)
  have hS:S.Nonempty:=by
    obtain ⟨r,hr⟩:=hoccurs
    exact ⟨r,by simp [S,hr]⟩
  let B:=factor (θ g0) (w g0) k
  have hp:=factor_properties (θ g0) (w g0) hg0 (hw g0) (hw1 g0) k
  refine ⟨B,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,?_⟩
  have he:retained e cls (fun r=>cValue (θ r) (2*k+1))
      (fun r=>aValue (θ r) (2*k+1)) w g0 (1/2)=BooleanRetainedRootReduction.matrix e S B:=by
    funext i j
    unfold retained BooleanRetainedRootReduction.matrix tensor
    apply Finset.prod_congr rfl
    intro r _
    by_cases hr:cls r=g0
    · simp [S,hr,B,factor]
    · simp [S,hr]
  rw [he] at retention
  exact ⟨(BooleanRetainedRootReduction.reduction basis e S hS B (fun i j=>(hp.2.1 i j).le)).trans
    ((HammingPottsToSource.toJointTarget basis M U (BooleanRetainedRootReduction.matrix e S B)).trans retention)⟩

end PlanarHom.BooleanBiasedFactorReduction
