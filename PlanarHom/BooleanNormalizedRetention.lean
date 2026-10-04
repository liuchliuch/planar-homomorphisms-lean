import PlanarHom.BooleanRetentionReduction
import PlanarHom.BooleanNormalizedFamilyIdentification
import PlanarHom.OracleReductionLaws

/-! NEW source normalization to retained classes. The odd exponent is chosen
from the genuine representative pairs, and the source-family simulation is
constructed from the actual original matrix by endpoint loops and distance
kernels. No source-availability premise is required. -/
noncomputable section
open Classical
namespace PlanarHom.BooleanNormalizedRetention
open Complexity Complexity.MixedCode FiniteLanguageAliases BooleanTensorSpectral
open BooleanEigenvalueBranches BooleanPDNormalization
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {b d q bt ut dimension : ℕ}

def cValue (θ : K) (t : ℕ) : K := (θ^t+(θ^t)⁻¹)/2
def aValue (θ : K) (t : ℕ) : K := (θ^t-(θ^t)⁻¹)/2

@[simp] theorem cValue_real (θ : K) (t : ℕ) :
    (cValue θ t : ℝ)=cParameter (θ : ℝ) t := by
  change K.val.toRingHom ((θ^t+(θ^t)⁻¹)/2) = _
  simp only [map_div₀,map_add,map_pow,map_inv₀,map_ofNat]
  rfl
@[simp] theorem aValue_real (θ : K) (t : ℕ) :
    (aValue θ t : ℝ)=aParameter (θ : ℝ) t := by
  change K.val.toRingHom ((θ^t-(θ^t)⁻¹)/2) = _
  simp only [map_div₀,map_sub,map_pow,map_inv₀,map_ofNat]
  rfl

theorem block_eq_normalForm (θ u : ℝ) (t : ℕ) :
    block (cParameter θ t) (aParameter θ t) u=normalForm (θ^t) u := by
  ext i j
  cases i <;> cases j <;>
    simp [block,traceless,Matrix.add_apply,Matrix.smul_apply,cParameter,aParameter,normalForm] <;> ring

theorem family_eq (M : Fin bt→Matrix (Fin q) (Fin q) K) (old : Fin bt)
    (e : Fin q≃(Fin d→Bool)) (γ : K) (hγ:0<(γ : ℝ))
    (cls : Fin d→Fin b) (θ w : Fin b→K)
    (hθ:∀i,1≤(θ i : ℝ)) (hw:∀i,0<(w i : ℝ)) (hw1:∀i,(w i : ℝ)<1)
    (hsource:Matrix.reindex e e (SpectralFieldPresentation.realMatrix (M old))=
      (γ : ℝ) • CubeTensorExponential.tensor
        (fun r=>normalForm (θ (cls r) : ℝ) (w (cls r) : ℝ))) (k : ℕ) (x : ℚ) :
    EndpointLoopParameterAvailability.family (M old) k ((γ^(2*k+1))⁻¹) x=
      fun i j=>BooleanInnerRecoveryCorrectness.sourceMatrix cls
        (fun r=>cValue (θ r) (2*k+1)) (fun r=>aValue (θ r) (2*k+1)) w x (e i) (e j) := by
  have h:=BooleanNormalizedFamilyIdentification.family_real (M old) e γ hγ
    (fun r=>(θ (cls r) : ℝ)) (fun r=>(w (cls r) : ℝ))
    (fun r=>lt_of_lt_of_le zero_lt_one (hθ (cls r)))
    (fun r=>hw (cls r)) (fun r=>hw1 (cls r)) hsource k x
  funext i j
  apply Subtype.ext
  have hij:=congrFun (congrFun h (e i)) (e j)
  have hm:=BooleanTensorRingMap.tensor_blocks_map K.val.toRingHom
    (fun r=>cValue (θ (cls r)) (2*k+1)) (fun r=>aValue (θ (cls r)) (2*k+1))
    (fun r=>w (cls r)*algebraMap ℚ K x)
  have hmij:=congrFun (congrFun hm (e i)) (e j)
  change (EndpointLoopParameterAvailability.family (M old) k ((γ^(2*k+1))⁻¹) x i j : ℝ)=
    K.val.toRingHom (tensor (fun r=>block (cValue (θ (cls r)) (2*k+1))
      (aValue (θ (cls r)) (2*k+1)) (w (cls r)*algebraMap ℚ K x)) (e i) (e j))
  rw [show K.val.toRingHom (tensor (fun r=>block (cValue (θ (cls r)) (2*k+1))
      (aValue (θ (cls r)) (2*k+1)) (w (cls r)*algebraMap ℚ K x)) (e i) (e j)) = _ from hmij]
  have hc (r:Fin b):K.val.toRingHom (cValue (θ r) (2*k+1))=cParameter (θ r : ℝ) (2*k+1):=cValue_real _ _
  have ha (r:Fin b):K.val.toRingHom (aValue (θ r) (2*k+1))=aParameter (θ r : ℝ) (2*k+1):=aValue_real _ _
  have hx:K.val.toRingHom (algebraMap ℚ K x)=(x:ℝ):=by
    change (algebraMap ℚ ℝ) x = (x:ℝ)
    simp
  simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    SpectralFieldPresentation.realMatrix,Matrix.map_apply,hc,ha,map_mul,hx,
    block_eq_normalForm,tensor,CubeTensorExponential.tensor] using hij

def originalSimulation (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M U (fun _=>1))
      (evaluationProblem basis M U (fun _=>1)) := by
  let h:=evaluationProblem_output_bound basis M U (fun _=>1)
  exact PromisePolyTimeTuringReduction.refl_of_output_bound _ (Classical.choose h) (Classical.choose_spec h)

/-- Genuine source access and fixed odd separation jointly give the retained
class label in the original source oracle. -/
theorem exists_retained_reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (old : Fin bt)
    (e : Fin q≃(Fin d→Bool)) (γ : K) (hγ:0<(γ : ℝ))
    (cls : Fin d→Fin b) (θ w : Fin b→K)
    (hθ:∀i,1≤(θ i : ℝ)) (hw:∀i,0<(w i : ℝ)) (hw1:∀i,(w i : ℝ)<1)
    (hrep:Function.Injective (fun i=>((θ i : ℝ),(w i : ℝ))))
    (hsource:Matrix.reindex e e (SpectralFieldPresentation.realMatrix (M old))=
      (γ : ℝ) • CubeTensorExponential.tensor
        (fun r=>normalForm (θ (cls r) : ℝ) (w (cls r) : ℝ)))
    (g0 : Fin b) (hg0:1<(θ g0 : ℝ)) (x0 : K) :
    ∃k:ℕ,Nonempty (PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (BooleanRetentionReduction.retained e cls
        (fun r=>cValue (θ r) (2*k+1)) (fun r=>aValue (θ r) (2*k+1)) w g0 x0)) U (fun _=>1))
      (evaluationProblem basis M U (fun _=>1))) := by
  obtain ⟨t,ht,ho,hp⟩:=BooleanExceptionalSource.exists_positive_odd_parameters
    (fun i=>(θ i : ℝ)) (fun i=>(w i : ℝ)) hθ hw hw1 hrep
  obtain ⟨k,hk⟩:=ho
  have he:t=2*k+1:=by omega
  subst t
  let c:=fun r=>cValue (θ r) (2*k+1)
  let a:=fun r=>aValue (θ r) (2*k+1)
  have hp':BooleanExceptionalSource.SeparatedParameters
      (fun i=>(c i : ℝ)) (fun i=>(a i : ℝ)) (fun i=>(w i : ℝ)):=by
    simpa only [c,a,cValue_real,aValue_real] using hp
  have ha:a g0≠0:=by
    intro hz
    have hp0:=BooleanEigenvalueBranches.aParameter_pos hg0 (by omega : 0<2*k+1)
    have hc:=congrArg (fun z:K=>(z : ℝ)) hz
    simp only [a,aValue_real,ZeroMemClass.coe_zero] at hc
    exact hp0.ne' hc
  let A:=M old
  let th:=fun r=>(θ (cls r) : ℝ)
  let ww:=fun r=>(w (cls r) : ℝ)
  have hth:∀r,0<th r:=fun r=>lt_of_lt_of_le zero_lt_one (hθ (cls r))
  have hww:∀r,0<ww r:=fun r=>hw (cls r)
  have hww1:∀r,ww r<1:=fun r=>hw1 (cls r)
  have hpd:=BooleanNormalizedFamilyIdentification.source_posDef A e γ hγ th ww hth hww hww1 hsource
  have hconn:=(BooleanNormalizedFamilyIdentification.sourceGraphIso A e γ hγ th ww hth hww hww1
    hsource).connected_iff.mpr (Boolean.cubeGraph_connected d)
  have hlog:=BooleanNormalizedFamilyIdentification.source_positive_log A e γ hγ th ww hth hww hww1 hsource
  let sim:=EndpointLoopParameterAvailability.reduction basis M U old k ((γ^(2*k+1))⁻¹)
    hpd hconn hlog (evaluationProblem basis M U (fun _=>1)) (originalSimulation basis M U)
  exact ⟨k,⟨BooleanRetentionReduction.available basis e M U cls c a w K.val.toRingHom hp' g0 ha x0
    _ (family_eq M old e γ hγ cls θ w hθ hw hw1 hsource k) _ sim⟩⟩

end PlanarHom.BooleanNormalizedRetention
