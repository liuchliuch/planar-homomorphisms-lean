import PlanarHom.BooleanRetentionQuerySemantics
import PlanarHom.BooleanRetentionPolynomial

/-! NEW complete nested interpolation correctness for the actual emitted
queries. The outer polynomial, degree, sample count and every inner premise are
derived from the graph and the fixed separated class parameters. -/
noncomputable section
open Classical
namespace PlanarHom.BooleanRetentionRecovery
open Complexity Complexity.MixedCode BooleanRetentionPrograms BooleanTensorPartitionMoments
open BooleanInnerRecoveryCorrectness BooleanSpectralCounts BooleanRetentionQuerySemantics
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {b d bt ut : ℕ}

theorem recoveryTable_eq (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (cls : Fin d→Fin b) (c a w : Fin b→K) (f : K→+*ℝ)
    (hp:BooleanExceptionalSource.SeparatedParameters
      (fun i=>f (c i)) (fun i=>f (a i)) (fun i=>f (w i)))
    (g0 : Fin b) (hg0:a g0≠0) :
    recoveryTable c a w (multiplicity cls) g0
      ((prepare selected.val c a w (multiplicity cls) g0 g).1,
       (prepare selected.val c a w (multiplicity cls) g0 g).2.map
          (sourceAnswer selected M U cls c a w)) =
    (BooleanEffectiveLengthSamples.samples c a w (multiplicity cls) (multiplicity cls g0)
      (g.markedCount selected.val)).map (fun q=>(algebraMap ℚ K q,
        (BooleanRetentionPolynomial.partition g hg selected M U (fun _=>1) cls c a w g0).eval
          (algebraMap ℚ K q))) := by
  let xs:=BooleanEffectiveLengthSamples.samples c a w (multiplicity cls) (multiplicity cls g0)
    (g.markedCount selected.val)
  let P:=BooleanRetentionPolynomial.partition g hg selected M U (fun _=>1) cls c a w g0
  change xs.zipIdx.map _ = xs.map (fun q=>(algebraMap ℚ K q,P.eval (algebraMap ℚ K q)))
  calc
    _ = xs.zipIdx.map (fun p=>(algebraMap ℚ K p.1,P.eval (algebraMap ℚ K p.1))) := by
      apply List.map_congr_left
      intro p hpidx
      have hq:p.1∈xs:=List.fst_mem_of_mem_zipIdx hpidx
      unfold recoveryRow
      dsimp only
      rw [answerBlock_eq g hg selected M U cls c a w g0 p.1 p.2 (by simpa only [prepare,xs,Prod.eta] using hpidx)]
      congr 1
      change BooleanInnerRecoveryProgram.recover c a w (multiplicity cls) g0
        ((g.markedCount selected.val,p.1),positiveMoments g hg selected M U (fun _=>1) cls c a w p.1) = _
      rw [recover_eq_retained g hg selected M U (fun _=>1) cls c a w f hp g0 hg0
        (multiplicity cls g0) p.1 hq]
      exact (BooleanRetentionPolynomial.eval_partition g hg selected M U (fun _=>1)
        cls c a w g0 (algebraMap ℚ K p.1)).symm
    _ = _ := by
      change xs.zipIdx.map ((fun q=>(algebraMap ℚ K q,P.eval (algebraMap ℚ K q))) ∘ Prod.fst)=_
      rw [←List.map_map,List.zipIdx_map_fst]

theorem recoverFinal_eq (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (cls : Fin d→Fin b) (c a w : Fin b→K) (f : K→+*ℝ)
    (hp:BooleanExceptionalSource.SeparatedParameters
      (fun i=>f (c i)) (fun i=>f (a i)) (fun i=>f (w i)))
    (g0 : Fin b) (hg0:a g0≠0) (x0 : K) :
    recoverFinal c a w (multiplicity cls) g0 x0
      ((prepare selected.val c a w (multiplicity cls) g0 g).1,
       (prepare selected.val c a w (multiplicity cls) g0 g).2.map
          (sourceAnswer selected M U cls c a w)) =
    g.evaluate hg (replace M selected
      (BooleanTensorSpectral.tensor (fun i=>if cls i=g0 then
        BooleanTensorSpectral.block (c (cls i)) (a (cls i)) (w (cls i)*x0) else 1))) U (fun _=>1) := by
  rw [recoverFinal,recoveryTable_eq g hg selected M U cls c a w f hp g0 hg0]
  let xs:=BooleanEffectiveLengthSamples.samples c a w (multiplicity cls) (multiplicity cls g0)
    (g.markedCount selected.val)
  let P:=BooleanRetentionPolynomial.partition g hg selected M U (fun _=>1) cls c a w g0
  have hn:(xs.map (algebraMap ℚ K)).Nodup:=
    (BooleanEffectiveLengthSamples.samples_nodup c a w (multiplicity cls) (multiplicity cls g0)
      (g.markedCount selected.val)).map (algebraMap ℚ K).injective
  have hd:P.degree<(xs.map (algebraMap ℚ K)).length:=by
    have hd0:=BooleanRetentionPolynomial.partition_degree g hg selected M U (fun _=>1) cls c a w g0
    have hl:=BooleanEffectiveLengthSamples.samples_length_ge f c a w (multiplicity cls)
      (multiplicity cls g0) (g.markedCount selected.val) hp
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    apply WithBot.coe_lt_coe.mpr
    simpa only [List.length_map] using Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hd0) hl
  have hr:=MaterializedPolynomialInterpolationMachines.recover_samples x0
    (xs.map (algebraMap ℚ K)) hn P hd
  rw [List.map_map] at hr
  exact hr.trans (BooleanRetentionPolynomial.eval_partition g hg selected M U (fun _=>1)
    cls c a w g0 x0)

end PlanarHom.BooleanRetentionRecovery
