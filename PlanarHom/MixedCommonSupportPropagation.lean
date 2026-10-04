import PlanarHom.FixedRealMixedRootRestriction
import PlanarHom.RootedColorRestriction

/-! Common support propagation for every retained binary label. Unary factors
are arbitrary and retained. Nonzero assignments force the selected binary
factor nonzero; no availability of an auxiliary union-support matrix is used. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MixedRootedRestriction
local instance (priority := 10000) mixedSupportDecEq (α:Type) : DecidableEq α := Classical.decEq α
open Complexity Complexity.MixedCode
variable {b u:ℕ} {C K:Type} [Fintype C] [Field K]

def CommonClosed (M:Fin b→Matrix C C K) (X:Set C) : Prop :=
  ∀l,RootedRestriction.ColorClosed (M l) X

theorem assignment_edge_nonzero (g:MixedCode) (hg:g.Valid b u) (M:Fin b→Matrix C C K)
    (U:Fin u→C→K) (w:C→K) (σ:Fin g.vertices→C)
    (h:(g.toMixedInstance hg).assignment M U w σ≠0) (e:Fin g.edges.length) :
    M ((g.toMixedInstance hg).edgeLabel e) (σ ((g.toMultiGraph hg).src e)) (σ ((g.toMultiGraph hg).dst e))≠0 := by
  have he:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).2
  exact (Finset.prod_ne_zero_iff.mp he) e (Finset.mem_univ e)

theorem assignment_adj_nonzero (g:MixedCode) (hg:g.Valid b u) (M:Fin b→Matrix C C K)
    (hs:∀l i j,M l i j=M l j i) (U:Fin u→C→K) (w:C→K) (σ:Fin g.vertices→C)
    (h:(g.toMixedInstance hg).assignment M U w σ≠0)
    (v z:Fin g.vertices) (hvz:(GraphComponentCode.support g).Adj v z) :
    ∃l:Fin b,M l (σ v) (σ z)≠0 := by
  obtain ⟨_,a,ha,hends|hends⟩:=hvz
  all_goals
    obtain ⟨i,hi⟩:=List.get_of_mem ha
    have hn:=assignment_edge_nonzero g hg M U w σ h i
    have hsrc:(g.toMultiGraph hg).src i=⟨a.1,(hg.1 a ha).1⟩:=by
      apply Fin.ext; simpa only [toMultiGraph] using congrArg Prod.fst hi
    have hdst:(g.toMultiGraph hg).dst i=⟨a.2.1,(hg.1 a ha).2.1⟩:=by
      apply Fin.ext; simpa only [toMultiGraph] using congrArg (fun a:ℕ×(ℕ×ℕ)=>a.2.1) hi
    rw [hsrc,hdst] at hn
  · have hv:(⟨a.1,(hg.1 a ha).1⟩:Fin g.vertices)=v:=Fin.ext hends.1
    have hz:(⟨a.2.1,(hg.1 a ha).2.1⟩:Fin g.vertices)=z:=Fin.ext hends.2
    exact ⟨_,by simpa only [hv,hz] using hn⟩
  · have hz:(⟨a.1,(hg.1 a ha).1⟩:Fin g.vertices)=z:=Fin.ext hends.1
    have hv:(⟨a.2.1,(hg.1 a ha).2.1⟩:Fin g.vertices)=v:=Fin.ext hends.2
    exact ⟨_,by simpa only [hv,hz,hs _ (σ z) (σ v)] using hn⟩

theorem colors_mem_of_root (g:MixedCode) (hg:g.Valid b u) (hc:(GraphComponentCode.support g).Connected)
    (r:Fin g.vertices) (M:Fin b→Matrix C C K) (hs:∀l i j,M l i j=M l j i)
    (U:Fin u→C→K) (w:C→K) (X:Set C) (hX:CommonClosed M X) (σ:Fin g.vertices→C)
    (hr:σ r∈X) (h:(g.toMixedInstance hg).assignment M U w σ≠0) : ∀v,σ v∈X := by
  intro v
  have hv:=(SimpleGraph.reachable_iff_reflTransGen r v).mp (hc.preconnected r v)
  induction hv with
  | refl=>exact hr
  | @tail z v _ hzv ih=>
    obtain ⟨l,hl⟩:=assignment_adj_nonzero g hg M hs U w σ h z v hzv
    exact hX l _ ih _ hl

theorem rootRestricted_eq_submatrix (g:MixedCode) (hg:g.Valid b u)
    (hc:(GraphComponentCode.support g).Connected) (r:Fin g.vertices)
    (M:Fin b→Matrix C C K) (hs:∀l i j,M l i j=M l j i) (U:Fin u→C→K) (w:C→K)
    (X:Set C) (hX:CommonClosed M X) :
    (g.toMixedInstance hg).rootRestricted r M U w X=
      g.evaluate hg (fun l (i j:X)=>M l i.val j.val) (fun l (i:X)=>U l i.val) (fun i:X=>w i.val) := by
  rw [evaluate_toMixedInstance]
  let G:=g.toMixedInstance hg
  let P:(Fin g.vertices→C)→Prop:=fun σ=>∀v,σ v∈X
  have hbad:∀σ:{σ:Fin g.vertices→C//¬P σ},
      (if σ.val r∈X then G.assignment M U w σ.val else 0)=0 := by
    intro σ
    by_cases hr:σ.val r∈X
    · simp only [hr,ite_true]
      by_contra hn
      exact σ.property (colors_mem_of_root g hg hc r M hs U w X hX σ.val hr hn)
    · simp [hr]
  unfold MixedInstance.rootRestricted MixedInstance.partition
  change (∑σ:Fin g.vertices→C,if σ r∈X then G.assignment M U w σ else 0)=
    ∑σ:Fin g.vertices→X,G.assignment (fun l (i j:X)=>M l i.val j.val) (fun l (i:X)=>U l i.val) (fun i:X=>w i.val) σ
  rw [←Fintype.sum_subtype_add_sum_subtype P (fun σ=>if σ r∈X then G.assignment M U w σ else 0)]
  simp only [hbad,Finset.sum_const_zero,add_zero]
  apply Fintype.sum_equiv (Equiv.subtypePiEquivPi (p:=fun (_:Fin g.vertices) i=>i∈X))
  intro σ
  have hr:=σ.property r
  simp only [hr,ite_true]
  rfl

/-- Literal union support. Components of this graph are closed under every
retained binary label, rather than under one distinguished matrix alone. -/
def commonSupport (M:Fin b→Matrix C C K) (hs:∀l i j,M l i j=M l j i) : SimpleGraph C where
  Adj i j:=i≠j ∧ ∃l,M l i j≠0
  symm:=by intro i j h; obtain ⟨l,hl⟩:=h.2; exact ⟨h.1.symm,l,by simpa only [hs l j i] using hl⟩
  loopless:=by intro i h; exact h.1 rfl

theorem component_commonClosed (M:Fin b→Matrix C C K) (hs:∀l i j,M l i j=M l j i)
    (c:(commonSupport M hs).ConnectedComponent) : CommonClosed M c.supp := by
  intro l i hi j hij
  by_cases he:i=j
  · simpa only [←he] using hi
  · exact c.mem_supp_of_adj_mem_supp hi ⟨he,l,hij⟩

end PlanarHom.MixedRootedRestriction
