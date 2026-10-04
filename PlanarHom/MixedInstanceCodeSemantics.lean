import PlanarHom.MixedInstanceEquivalence
import PlanarHom.MixedPlanarCode

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode
variable {b u:ℕ}

def toMixedInstance (g:MixedCode) (hg:g.Valid b u) :
    MixedInstance (Fin g.vertices) (Fin g.edges.length) (Fin g.unaries.length) b u where
  graph:=g.toMultiGraph hg
  edgeLabel e:=⟨(g.edges.get e).2.2,(hg.1 _ (List.get_mem _ e)).2.2⟩
  unaryHost f:=⟨(g.unaries.get f).1,(hg.2 _ (List.get_mem _ f)).1⟩
  unaryLabel f:=⟨(g.unaries.get f).2,(hg.2 _ (List.get_mem _ f)).2⟩

variable {C K:Type} [Fintype C] [Field K]

theorem evaluate_toMixedInstance (g:MixedCode) (hg:g.Valid b u) (M:Fin b→Matrix C C K)
    (U:Fin u→C→K) (w:C→K) : g.evaluate hg M U w=(g.toMixedInstance hg).partition M U w := by
  unfold evaluate MixedInstance.partition MixedInstance.assignment
  apply Finset.sum_congr
  · ext σ; simp
  intro σ hσ
  congr 1
  · congr 1
    rw [←Fin.prod_univ_fun_getElem]
    apply Finset.prod_congr rfl
    intro e he
    have hv:=hg.1 (g.edges.get e) (List.get_mem _ e)
    simp only [List.get_eq_getElem] at hv
    simp only [binaryValue,dif_pos hv,toMixedInstance,toMultiGraph,List.get_eq_getElem]
  · rw [←Fin.prod_univ_fun_getElem]
    apply Finset.prod_congr rfl
    intro f hf
    have hv:=hg.2 (g.unaries.get f) (List.get_mem _ f)
    simp only [List.get_eq_getElem] at hv
    simp only [unaryValue,dif_pos hv,toMixedInstance,List.get_eq_getElem]

end PlanarHom.Complexity.MixedCode
