import PlanarHom.HeterogeneousGraphReduction
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.ZeroWeights

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode
open PairProjectionMachines
variable {C D R : Type} [Fintype C] [Fintype D] [CommSemiring R] {bt ut : ℕ}

theorem evaluate_restrict_zero_weights (g : MixedCode) (hg : g.Valid bt ut)
    (M : Fin bt→Matrix C C R) (U : Fin ut→C→R) (w : C→R)
    (S : C→Prop) [Fintype {c//S c}] (hw : ∀ c,¬S c→w c=0) :
    g.evaluate hg M U w=g.evaluate hg
      (fun l (i j : {c//S c})=>M l i.val j.val)
      (fun l (i : {c//S c})=>U l i.val) (fun (i : {c//S c})=>w i.val) := by
  let P : (Fin g.vertices→C)→Prop := fun σ=>∀v,S (σ v)
  let f : (Fin g.vertices→C)→R := fun σ=>(∏v,w (σ v))*
    (g.edges.map (binaryValue g.vertices bt M σ)).prod*
    (g.unaries.map (unaryValue g.vertices ut U σ)).prod
  have hbad : ∀ σ : {σ : Fin g.vertices→C // ¬P σ},f σ.val=0 := by
    intro σ
    obtain ⟨v,hv⟩ : ∃v,¬S (σ.val v) := by simpa only [P,not_forall] using σ.property
    have hp : (∏v,w (σ.val v))=0 := Finset.prod_eq_zero (Finset.mem_univ v) (hw _ hv)
    simp only [f,hp,zero_mul]
  change (∑σ : Fin g.vertices→C,f σ)=_
  calc
    _ = ∑σ : {σ : Fin g.vertices→C // P σ},f σ.val := by
      rw [←Fintype.sum_subtype_add_sum_subtype P f]
      simp only [hbad,Finset.sum_const_zero,add_zero]
    _ = _ := by
      apply Fintype.sum_equiv (Equiv.subtypePiEquivPi (p:=fun (_:Fin g.vertices) c=>S c))
      intro σ
      rfl

theorem evaluate_zero_background (g : MixedCode) (hg : g.Valid bt ut)
    (M : Fin bt→Matrix C C R) (U : Fin ut→C→R) :
    g.evaluate hg M U (fun _=>0)=if g.vertices=0 then 1 else 0 := by
  by_cases hz : g.vertices=0
  · have he : g.edges=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e he
      have h := (hg.1 e he).1
      omega
    have hu : g.unaries=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro u hu
      have h := (hg.2 u hu).1
      omega
    simp [evaluate,hz,he,hu]
  · letI : Nonempty (Fin g.vertices) := ⟨⟨0,Nat.pos_of_ne_zero hz⟩⟩
    simp [evaluate,hz]

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

def sameGraphColorReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (MT : Fin bt→Matrix C C K) (UT : Fin ut→C→K) (wT : C→K)
    (MS : Fin bt→Matrix D D K) (US : Fin ut→D→K) (wS : D→K)
    (he : ∀g : MixedCode,∀ (hg:g.Valid bt ut),g.evaluate hg MS US wS=g.evaluate hg MT UT wT) :
    PromisePolyTimeTuringReduction (evaluationProblem basis MT UT wT)
      (evaluationProblem basis MS US wS) := by
  apply planarReductionOfHeterogeneousPipeline basis BitEncoding.bits MT UT wT MS US wS
    (fun g=>([],[g])) (fun p : Bits×List K=>p.2.sum)
  · have hl := ((fp_id encoding).pair (fp_const encoding encoding.list [])).comp
      (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    simpa only [List.mem_singleton.mp hq] using hg
  · intro g hg
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [totalEvaluation_valid _ _ _ _ hg.1]
    exact he g hg.1

variable (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix C C K) (U : Fin ut→C→K) (w : C→K)
    (S : C→Prop) [Fintype {c//S c}] (hw : ∀ c,¬S c→w c=0)

def removeZeroWeightsReduction :
    PromisePolyTimeTuringReduction (evaluationProblem basis M U w)
      (evaluationProblem basis (fun l (i j:{c//S c})=>M l i.val j.val)
        (fun l (i:{c//S c})=>U l i.val) (fun (i:{c//S c})=>w i.val)) :=
  sameGraphColorReduction basis M U w _ _ _
    (fun g hg=>(evaluate_restrict_zero_weights g hg M U w S hw).symm)

def restoreZeroWeightsReduction :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun l (i j:{c//S c})=>M l i.val j.val)
        (fun l (i:{c//S c})=>U l i.val) (fun (i:{c//S c})=>w i.val))
      (evaluationProblem basis M U w) :=
  sameGraphColorReduction basis _ _ _ M U w
    (fun g hg=>evaluate_restrict_zero_weights g hg M U w S hw)

end PlanarHom.Complexity.MixedCode
