import PlanarHom.BooleanRetentionRecovery
import PlanarHom.FixedToParameterizedGraphReduction
import PlanarHom.MixedColorEquivalence

/-! NEW actual class-retention oracle reduction. A source-family simulator is
used with its original companion labels and unit backgrounds; the fixed target
retains exactly one Boolean class. No moment oracle or target simulator is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.BooleanRetentionReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases BooleanTensorPartitionMoments
open BooleanRetentionPrograms BooleanRetentionQuerySemantics BooleanSpectralCounts
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {b d q bt ut dimension : ℕ}

def chartMatrices (e : Fin q≃(Fin d→Bool)) (M : Fin bt→Matrix (Fin q) (Fin q) K) :
    Fin (bt+1)→Matrix (Fin d→Bool) (Fin d→Bool) K :=
  appendOne (fun l i j=>M l (e.symm i) (e.symm j)) 0

def retained (e : Fin q≃(Fin d→Bool)) (cls : Fin d→Fin b) (c a w : Fin b→K)
    (g0 : Fin b) (x0 : K) : Matrix (Fin q) (Fin q) K :=
  fun i j=>BooleanTensorSpectral.tensor (fun k=>if cls k=g0 then
    BooleanTensorSpectral.block (c (cls k)) (a (cls k)) (w (cls k)*x0) else 1) (e i) (e j)

theorem chart_evaluate (e : Fin q≃(Fin d→Bool)) (g : MixedCode) (hg:g.Valid (bt+1) ut)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K)
    (A : Matrix (Fin d→Bool) (Fin d→Bool) K) :
    g.evaluate hg (replace (chartMatrices e M) (Fin.last bt) A)
      (fun l i=>U l (e.symm i)) (fun _=>1) =
    g.evaluate hg (appendOne M (fun i j=>A (e i) (e j))) U (fun _=>1) := by
  have hM:replace (chartMatrices e M) (Fin.last bt) A=
      fun l i j=>appendOne M (fun i j=>A (e i) (e j)) l (e.symm i) (e.symm j):=by
    funext l
    refine Fin.lastCases ?_ (fun k=>?_) l
    · ext i j
      simp [replace]
    · have hk:k.castSucc≠Fin.last bt:=by
        intro h
        have hv:=congrArg Fin.val h
        simp only [Fin.coe_castSucc,Fin.val_last] at hv
        exact k.isLt.ne hv
      simp only [replace,hk,if_false,chartMatrices]
      change appendOne (fun l i j=>M l (e.symm i) (e.symm j)) 0 (Fin.castAdd 1 k) =
        fun i j=>appendOne M (fun i j=>A (e i) (e j)) (Fin.castAdd 1 k) (e.symm i) (e.symm j)
      simp only [appendOne_old]
  rw [hM]
  exact evaluate_color_equiv e.symm g hg _ U (fun _=>1)

theorem sourceAnswer_eq (e : Fin q≃(Fin d→Bool))
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K)
    (cls : Fin d→Fin b) (c a w : Fin b→K)
    (F : ℚ→Matrix (Fin q) (Fin q) K)
    (hF:∀x,F x=fun i j=>BooleanInnerRecoveryCorrectness.sourceMatrix cls c a w x (e i) (e j))
    (p : Query) :
    sourceAnswer (Fin.last bt) (chartMatrices e M) (fun l i=>U l (e.symm i)) cls c a w p =
      ParameterizedMatrixEvaluation.answer M U (fun _=>1) F p := by
  unfold sourceAnswer ParameterizedMatrixEvaluation.answer totalEvaluation
  split
  · rw [hF p.1]
    exact chart_evaluate e p.2 (by assumption) M U _
  · rfl

def reduction (basis : Module.Basis (Fin dimension) ℚ K) (e : Fin q≃(Fin d→Bool))
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K)
    (cls : Fin d→Fin b) (c a w : Fin b→K) (f : K→+*ℝ)
    (hp:BooleanExceptionalSource.SeparatedParameters
      (fun i=>f (c i)) (fun i=>f (a i)) (fun i=>f (w i)))
    (g0 : Fin b) (hg0:a g0≠0) (x0 : K)
    (F : ℚ→Matrix (Fin q) (Fin q) K)
    (hF:∀x,F x=fun i j=>BooleanInnerRecoveryCorrectness.sourceMatrix cls c a w x (e i) (e j))
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis BitEncoding.rat M U (fun _=>1) F (fun x=>0<x)) base) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (retained e cls c a w g0 x0)) U (fun _=>1))
      (ParameterizedMatrixEvaluation.problem basis BitEncoding.rat M U (fun _=>1) F (fun x=>0<x)) := by
  apply FixedToParameterizedGraphReduction.reductionOfPipeline basis BitEncoding.rat metaEncoding
    (appendOne M (retained e cls c a w g0 x0)) U (fun _=>1) M U (fun _=>1) F (fun x=>0<x)
    (prepare bt c a w (multiplicity cls) g0) (recoverFinal c a w (multiplicity cls) g0 x0)
    (fp_prepare basis bt c a w (multiplicity cls) g0)
    (fp_recoverFinal basis c a w (multiplicity cls) g0 x0) ?_ ?_ base simulation
  · intro g hg z hz
    obtain ⟨hq,hzplan⟩:=prepare_queries_planar cls c a w g0 (Fin.last bt) g hg z hz
    have hb:=BooleanEffectiveLengthSamples.samples_bounds c a w (multiplicity cls)
      (multiplicity cls g0) (g.markedCount bt) z.1 hq
    exact ⟨by exact_mod_cast hb.1.1,hzplan⟩
  · intro g hg
    have hr:=BooleanRetentionRecovery.recoverFinal_eq g hg.1 (Fin.last bt)
      (chartMatrices e M) (fun l i=>U l (e.symm i)) cls c a w f hp g0 hg0 x0
    have hs:sourceAnswer (Fin.last bt) (chartMatrices e M) (fun l i=>U l (e.symm i)) cls c a w =
        ParameterizedMatrixEvaluation.answer M U (fun _=>1) F:=by
      funext p
      exact sourceAnswer_eq e M U cls c a w F hF p
    rw [hs] at hr
    exact hr.trans (chart_evaluate e g hg.1 M U _)

def available (basis : Module.Basis (Fin dimension) ℚ K) (e : Fin q≃(Fin d→Bool))
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K)
    (cls : Fin d→Fin b) (c a w : Fin b→K) (f : K→+*ℝ)
    (hp:BooleanExceptionalSource.SeparatedParameters
      (fun i=>f (c i)) (fun i=>f (a i)) (fun i=>f (w i)))
    (g0 : Fin b) (hg0:a g0≠0) (x0 : K)
    (F : ℚ→Matrix (Fin q) (Fin q) K)
    (hF:∀x,F x=fun i j=>BooleanInnerRecoveryCorrectness.sourceMatrix cls c a w x (e i) (e j))
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis BitEncoding.rat M U (fun _=>1) F (fun x=>0<x)) base) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (retained e cls c a w g0 x0)) U (fun _=>1)) base :=
  (reduction basis e M U cls c a w f hp g0 hg0 x0 F hF base simulation).trans simulation

end PlanarHom.BooleanRetentionReduction
