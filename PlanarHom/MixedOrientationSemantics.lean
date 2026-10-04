import PlanarHom.MixedOrientationMetadata
import PlanarHom.HomogeneousSourceOrientationCrossing

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MixedOrientation
open Complexity Complexity.MixedCode PrescribedDomains GraphComponentCode
open HomogeneousSourceOrientation FixedRealRootRestrictions MixedRootedRestriction
variable {b u:ℕ} {C K:Type} [Fintype C] [Field K]

theorem assignment_raw (g:MixedCode) (hg:g.Valid b u) (M:Fin b→Matrix C C K)
    (U:Fin u→C→K) (w:C→K) (σ:Fin g.vertices→C) :
    (g.toMixedInstance hg).assignment M U w σ=GraphComponentCode.assignmentWeight g M U w σ := by
  unfold MixedInstance.assignment GraphComponentCode.assignmentWeight
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

theorem proper_support (g:MixedCode) (hg:g.Valid b (u+2)) (δ:Fin g.vertices→Fin 2) (hp:Proper g hg δ) :
    ∀v z,(support g).Adj v z→decide (δ v=1)≠decide (δ z=1) := by
  intro v z hvz heq
  have hδ:δ v=δ z:=by
    have ha:=(δ v).isLt
    have hb:=(δ z).isLt
    have hi:Function.Injective (fun d:Fin 2=>decide (d=1)):=by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp_all
    exact hi heq
  obtain ⟨_,a,ha,hends|hends⟩:=hvz
  all_goals
    have hn:=hp a ha
  · have hv:(⟨a.1,(hg.1 a ha).1⟩:Fin g.vertices)=v:=Fin.ext hends.1
    have hz:(⟨a.2.1,(hg.1 a ha).2.1⟩:Fin g.vertices)=z:=Fin.ext hends.2
    exact hn (by simpa only [hv,hz] using hδ)
  · have hz:(⟨a.1,(hg.1 a ha).1⟩:Fin g.vertices)=z:=Fin.ext hends.1
    have hv:(⟨a.2.1,(hg.1 a ha).2.1⟩:Fin g.vertices)=v:=Fin.ext hends.2
    exact hn (by simpa only [hv,hz] using hδ.symm)

theorem sides_eq_of_root (g:MixedCode) (hg:g.Valid b u) (hc:(support g).Connected)
    (r:Fin g.vertices) (M:Fin b→Matrix C C K) (hs:∀l i j,M l i j=M l j i)
    (U:Fin u→C→K) (w:C→K) (side:C→Bool) (hcross:∀l i j,M l i j≠0→side i≠side j)
    (δ:Fin g.vertices→Bool) (hp:∀v z,(support g).Adj v z→δ v≠δ z)
    (σ:Fin g.vertices→C) (hr:side (σ r)=δ r) (h:(g.toMixedInstance hg).assignment M U w σ≠0) :
    ∀v,side (σ v)=δ v := by
  intro v
  have hv:=(SimpleGraph.reachable_iff_reflTransGen r v).mp (hc.preconnected r v)
  induction hv with
  | refl=>exact hr
  | @tail z v _ hzv ih=>
    obtain ⟨l,hl⟩:=assignment_adj_nonzero g hg M hs U w σ h z v hzv
    exact bool_agreement_across_edge (hcross l _ _ hl) (hp z v hzv) ih

theorem restricted_eq_root (g:MixedCode) (hg:g.Valid b u) (hc:(support g).Connected)
    (r:Fin g.vertices) (M:Fin b→Matrix C C K) (hs:∀l i j,M l i j=M l j i)
    (U:Fin u→C→K) (w:C→K) (side:C→Bool) (hcross:∀l i j,M l i j≠0→side i≠side j)
    (δ:Fin g.vertices→Fin 2) (hp:∀v z,(support g).Adj v z→decide (δ v=1)≠decide (δ z=1)) :
    evaluateRestricted g hg M U w (Bipartite.domains side) δ=
      (g.toMixedInstance hg).rootRestricted r M U w (Bipartite.domains side (δ r)) := by
  unfold evaluateRestricted MixedInstance.rootRestricted
  apply Finset.sum_congr
  · ext σ; simp
  intro σ hσ
  change (if Allowed (Bipartite.domains side) δ σ then GraphComponentCode.assignmentWeight g M U w σ else 0)=_
  rw [←assignment_raw g hg M U w σ]
  by_cases hz:(g.toMixedInstance hg).assignment M U w σ=0
  · simp [hz]
  · have he:side (σ r)=decide (δ r=1) ↔ ∀v,side (σ v)=decide (δ v=1):=
      ⟨fun hr=>sides_eq_of_root g hg hc r M hs U w side hcross _ hp σ hr hz,fun h=>h r⟩
    simp only [Allowed,Bipartite.domains,Set.mem_setOf_eq]
    congr 1
    exact propext he.symm

theorem evaluate_tags (g:MixedCode) (hg:g.Valid b (u+2)) (δ:Fin g.vertices→Fin 2) (ht:Tags u g δ)
    (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) (side:C→Bool) :
    g.evaluate hg M (extendedUnaries U (Bipartite.domains side)) w=
      (withDomains (unaryTypes:=u) (strip u g) δ).evaluate
        (withDomains_valid _ (strip_valid g hg) δ) M (extendedUnaries U (Bipartite.domains side)) w := by
  unfold evaluate
  apply Finset.sum_congr
  · ext σ; simp
  intro σ hσ
  congr 1
  exact (ht.map (unaryValue g.vertices (u+2) (extendedUnaries U (Bipartite.domains side)) σ)).prod_eq

theorem tagged_eq_root (g:MixedCode) (hg:g.Valid b (u+2)) (δ:Fin g.vertices→Fin 2)
    (ht:Tags u g δ) (hp:Proper g hg δ) (hc:(support g).Connected) (r:Fin g.vertices)
    (M:Fin b→Matrix C C K) (hs:∀l i j,M l i j=M l j i)
    (U:Fin u→C→K) (w:C→K) (side:C→Bool) (hcross:∀l i j,M l i j≠0→side i≠side j) :
    g.evaluate hg M (extendedUnaries U (Bipartite.domains side)) w=
      ((strip u g).toMixedInstance (strip_valid g hg)).rootRestricted r M U w (Bipartite.domains side (δ r)) := by
  rw [evaluate_tags g hg δ ht,evaluate_withDomains]
  exact restricted_eq_root _ (strip_valid g hg) hc r M hs U w side hcross δ (proper_support g hg δ hp)

end PlanarHom.MixedOrientation
