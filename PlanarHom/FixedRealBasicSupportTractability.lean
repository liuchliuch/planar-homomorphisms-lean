import PlanarHom.FixedRealBasicConnected
import PlanarHom.RepresentedBitFPClosure

/-! NEW A.9 easy algorithm: sum the actual fixed basic target-component
computers on each computed input component, then multiply represented answers.
This includes every isolate and the empty graph; no positivity is needed by
the easy-side arithmetic itself. -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealBasicComponents
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open ZeroOneBasicTractability RootedRestriction FixedRealComponents
variable {n e:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

theorem support_computer (M:Matrix C C K) (hs:∀i j,M i j=M j i) (w:C→K)
    (h:∀c:(colorSupport M hs).ConnectedComponent,
      FieldBasicZeroOneComponent (fun i j:c.supp=>M i.val j.val)) :
    Nonempty (ConnectedComputer basis M w) := by
  let I:=(colorSupport M hs).ConnectedComponent
  let comp:∀c:I,ConnectedComputer basis (fun i j:c.supp=>M i.val j.val) (fun i:c.supp=>w i.val):=
    fun c=>Classical.choice (basic_computer basis _ _ (h c))
  let number:I≃Fin (Fintype.card I):=Fintype.equivFin I
  let codes:=fun g:MixedCode=>List.ofFn (fun j:Fin (Fintype.card I)=>(comp (number.symm j)).run g)
  let ops:=FixedRealRootRestriction.arithmetic basis
  let run:=fun g=>ops.dot (Fintype.card I) (fun _=>constCode basis 1) (codes g)
  have hc:FP MixedCode.encoding (encoding n e).list codes := by
    have hv:=FixedVectorMachines.fp_assemble MixedCode.encoding (encoding n e) (Fintype.card I)
      (fun g j=>(comp (number.symm j)).run g) (fun j=>(comp (number.symm j)).fp)
    have he:FP ((encoding n e).vector (Fintype.card I)) (encoding n e).list List.ofFn:=
      fp_code_view _ _ _ (fun _=>rfl)
    exact hv.comp he
  have hf:FP MixedCode.encoding (encoding n e) run:=hc.comp (ops.fp_dot _ _)
  have hspec (g:MixedCode) : Valid n (run g) ∧
      value basis (run g)=∑j:Fin (Fintype.card I),value basis ((comp (number.symm j)).run g) := by
    have hh:=ops.dot_ofFn (Fintype.card I) (fun _=>constCode basis 1)
      (fun j=>(comp (number.symm j)).run g) (fun _=>constant_valid basis 1)
      (fun j=>(comp (number.symm j)).valid g)
    have hv:value basis (run g)=∑j:Fin (Fintype.card I),
        value basis (constCode basis 1)*value basis ((comp (number.symm j)).run g) := hh.2
    exact ⟨hh.1,by simpa only [constant_value,one_mul] using hv⟩
  refine ⟨⟨run,hf,(fun g=>(hspec g).1),?_⟩⟩
  intro g hg hconn hn
  rw [(hspec g).2]
  calc
    (∑j:Fin (Fintype.card I),value basis ((comp (number.symm j)).run g))=
        ∑j:Fin (Fintype.card I),g.evaluate hg
          (fun _:Fin 1=>fun i k:(number.symm j).supp=>M i.val k.val)
          (fun i:Fin 0=>i.elim0) (fun i:(number.symm j).supp=>w i.val) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (comp (number.symm j)).correct g hg hconn hn
    _ = ∑c:I,g.evaluate hg (fun _:Fin 1=>fun i j:c.supp=>M i.val j.val)
        (fun i:Fin 0=>i.elim0) (fun i:c.supp=>w i.val) :=
      number.symm.sum_comp (fun c:I=>g.evaluate hg
        (fun _:Fin 1=>fun i j:c.supp=>M i.val j.val) (fun i:Fin 0=>i.elim0) (fun i:c.supp=>w i.val))
    _ = g.evaluate hg (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w :=
      (evaluate_eq_sum_supportBlocks g hg hconn hn M hs w).symm

theorem basic_support_inFP (M:Matrix C C K) (hs:∀i j,M i j=M j i) (w:C→K)
    (h:∀c:(colorSupport M hs).ConnectedComponent,
      FieldBasicZeroOneComponent (fun i j:c.supp=>M i.val j.val)) :
    (FixedRealComponents.problem basis (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w).InFP := by
  let c:=Classical.choice (support_computer basis M hs w h)
  have hc:(FixedRealComponents.connectedProblem basis (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w).InFP := by
    apply Presentation.problem_inFP _ _ MixedCode.normalizer _ _ c.run c.fp (fun g _=>c.valid g)
    intro g hg
    rw [totalEvaluation_valid _ _ _ g hg.1.1]
    exact c.correct g hg.1.1 hg.2.1 hg.2.2
  exact (FixedRealComponents.componentReduction basis (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w).inFP hc

end PlanarHom.FixedRealBasicComponents
