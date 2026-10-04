import PlanarHom.FixedRealPositiveRatioChart
import PlanarHom.FixedRealBipartiteRatioChart
import PlanarHom.FixedRealMixedInterpolation
import PlanarHom.Structures

/-! NEW full A.6 easy direction in the prescribed represented real field.
Every source parameter is an original-field entry ratio, and all block,
tensor, degree, orientation and component computers are genuine bit programs. -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical
namespace PlanarHom.FixedRealGraphEvaluation
open Complexity DensePolynomial Structures BooleanTensorEasyAssembly
variable {n e:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K) (φ:K→+*ℝ)

 theorem allowedBlock (M:Matrix C C K) (h:Structures.AllowedBlock (fun i j=>φ (M i j))) :
    Evaluable basis M (fun _=>1) := by
  letI:CharZero K:=φ.charZero
  cases h with
  | zero e0 hz=>
    have hm:M=0:=by funext i j;apply φ.injective;simpa using hz i j
    let f:C≃Fin 1:=e0.trans (Equiv.ofUnique Unit (Fin 1))
    have hf:=color basis f (fun _ _:Fin 1=>(0:K)*(0:K)) (fun _=>1)
      (rankOne basis (fun _:Fin 1=>(0:K)) (fun _=>1))
    simpa only [hm,zero_mul,Matrix.zero_apply] using hf
  | positive k d hk a ρ ha hρ f hm=>
    have hsource:Matrix.reindex f f (fun i j=>φ (M i j))=
        fun p r=>a p.1*a r.1*Boolean.tensor ρ p.2 r.2:=by
      ext i j
      simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,f.apply_symm_apply] using hm (f.symm i) (f.symm j)
    obtain ⟨γ,α,p,hp⟩:=positive_ratios φ M ⟨0,hk⟩ f a ha ρ hsource
    let T:=BooleanTensorSpectral.tensor (fun r=>isingMatrix (p r))
    let B:=MultiGraph.tensorInteraction (fun i j=>α i*α j) T
    have ht:Evaluable basis T (fun _=>1):=tensor basis (fun r=>isingMatrix (p r))
      (fun r=>ising basis (Rat.castHom K) (p r))
    have hb:Evaluable basis B (fun _=>1):=by
      have hprod:=product basis (fun i j=>α i*α j) T (fun _=>1) (fun _=>1)
        (rankOne basis α (fun _=>1)) ht
      have hw:MultiGraph.tensorVertexWeight (fun _:Fin k=>(1:K)) (fun _:Boolean.Cube d=>(1:K))=(fun _=>1):=by
        funext x
        exact mul_one _
      rw [hw] at hprod
      exact hprod
    have hh:=color basis f (γ • B) (fun _=>1) (scalar basis γ B hb)
    have heq:M=fun i j=>(γ • B) (f i) (f j):=by
      funext i j
      exact hp i j
    simpa only [heq] using hh
  | bipartite k l d hk hl a b ρ ha hb hρ f hm=>
    have hsource:Matrix.reindex f f (fun i j=>φ (M i j))=
        MultiGraph.tensorInteraction (BipartiteRankTwoTractability.matrix a b) (Boolean.tensor ρ):=by
      ext i j
      simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,f.apply_symm_apply] using hm (f.symm i) (f.symm j)
    obtain ⟨α,β,p,hp⟩:=bipartite_ratios φ M ⟨0,hk⟩ ⟨0,hl⟩ f a b ha hb ρ hsource
    let T:=BooleanTensorSpectral.tensor (fun r=>isingMatrix (p r))
    let B:=MultiGraph.tensorInteraction (BipartiteRankTwoTractability.matrix α β) T
    have ht:Evaluable basis T (fun _=>1):=tensor basis (fun r=>isingMatrix (p r))
      (fun r=>ising basis (Rat.castHom K) (p r))
    have hw:(Sum.elim (fun _:Fin k=>(1:K)) (fun _:Fin l=>(1:K)))=(fun _=>1):=by
      funext i
      cases i <;> rfl
    have hbip:Evaluable basis (BipartiteRankTwoTractability.matrix α β) (fun _=>1):=by
      simpa only [hw] using bipartite basis α (fun _=>1) β (fun _=>1)
    have hB:Evaluable basis B (fun _=>1):=by
      have hprod:=product basis (BipartiteRankTwoTractability.matrix α β) T (fun _=>1) (fun _=>1) hbip ht
      have hwprod:MultiGraph.tensorVertexWeight (fun _:Fin k⊕Fin l=>(1:K)) (fun _:Boolean.Cube d=>(1:K))=(fun _=>1):=by
        funext x
        exact mul_one _
      rw [hwprod] at hprod
      exact hprod
    have hh:=color basis f B (fun _=>1) hB
    have heq:M=fun i j=>B (f i) (f j):=funext (fun i=>funext (hp i))
    simpa only [heq] using hh

 theorem nonnegativeClass (M:Matrix C C K) (h:Structures.NonnegativeClass (fun i j=>φ (M i j))) :
    Evaluable basis M (fun _=>1) := by
  have hs:=h.symmetric
  obtain ⟨t,block,honto,hzero,hforms⟩:=h
  letI:DecidableEq (Fin t):=Classical.decEq _
  apply fibers basis block M (fun i j=>φ.injective (hs i j))
    (fun i j h=>φ.injective (by simpa using hzero i j h)) (fun _=>1)
  intro r
  exact allowedBlock basis φ (fun i j:{i // block i=r}=>M i.val j.val) (hforms r)

end PlanarHom.FixedRealGraphEvaluation
namespace PlanarHom.FixedRealApproximation
open DensePolynomial
variable {n e q:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

 theorem theoremA6_easy (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (φ:K→+*ℝ) (M:Matrix (Fin q) (Fin q) K)
    (h:Structures.NonnegativeClass (fun i j=>φ (M i j))) :
    (FixedRealMixedInterpolation.problem basis (fun _:Fin 1=>M)
      (fun u:Fin 0=>u.elim0) (fun _=>1)).InFP :=
  FixedRealGraphEvaluation.inFP basis M (fun _=>1) (FixedRealGraphEvaluation.nonnegativeClass basis φ M h)

end PlanarHom.FixedRealApproximation
