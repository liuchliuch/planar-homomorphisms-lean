import PlanarHom.RootedHomogeneousSemantics
import PlanarHom.RootedConditionalSemantics
import PlanarHom.GraphComponentConnectivity

/-! On a connected input, one root restriction to a union of source support
components forces every nonzero assignment into that color set. Signs of edge
weights play no role in this termwise implication. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.RootedRestriction
local instance (priority := 10000) rootedColorRestrictionDecEq0 (α : Type*) : DecidableEq α := Classical.decEq α
open Complexity Complexity.MixedCode
variable {C K : Type} [Fintype C] [Field K]

def ColorClosed (M : Matrix C C K) (X : Set C) : Prop :=
  ∀ i ∈ X, ∀ j, M i j ≠ 0 → j ∈ X

omit [Fintype C] in
theorem assignment_edge_ne_zero (g : MixedCode) (hg : g.Valid 1 0)
    (M : Matrix C C K) (w : C → K) (σ : Fin g.vertices → C)
    (h : (g.toMultiGraph hg).assignmentWeight M w σ ≠ 0) (e : Fin g.edges.length) :
    M (σ ((g.toMultiGraph hg).src e)) (σ ((g.toMultiGraph hg).dst e)) ≠ 0 := by
  have hp := (mul_ne_zero_iff.mp h).2
  exact (Finset.prod_ne_zero_iff.mp hp) e (Finset.mem_univ e)

theorem assignment_adj_ne_zero (g : MixedCode) (hg : g.Valid 1 0)
    (M : Matrix C C K) (hs : ∀ i j,M i j=M j i) (w : C → K) (σ : Fin g.vertices → C)
    (h : (g.toMultiGraph hg).assignmentWeight M w σ ≠ 0)
    (u v : Fin g.vertices) (huv : (GraphComponentCode.support g).Adj u v) :
    M (σ u) (σ v) ≠ 0 := by
  obtain ⟨_,e,he,hends|hends⟩ := huv
  all_goals
    obtain ⟨k,hk⟩ := List.get_of_mem he
    have hn := assignment_edge_ne_zero g hg M w σ h k
    have hsrc : (g.toMultiGraph hg).src k = ⟨e.1,(hg.1 e he).1⟩ := by
      apply Fin.ext; simpa only [toMultiGraph] using congrArg Prod.fst hk
    have hdst : (g.toMultiGraph hg).dst k = ⟨e.2.1,(hg.1 e he).2.1⟩ := by
      apply Fin.ext; simpa only [toMultiGraph] using congrArg (fun a : ℕ × (ℕ × ℕ) => a.2.1) hk
    rw [hsrc,hdst] at hn
  · have hu : (⟨e.1,(hg.1 e he).1⟩ : Fin g.vertices)=u := Fin.ext hends.1
    have hv : (⟨e.2.1,(hg.1 e he).2.1⟩ : Fin g.vertices)=v := Fin.ext hends.2
    simpa only [hu,hv] using hn
  · have hv : (⟨e.1,(hg.1 e he).1⟩ : Fin g.vertices)=v := Fin.ext hends.1
    have hu : (⟨e.2.1,(hg.1 e he).2.1⟩ : Fin g.vertices)=u := Fin.ext hends.2
    simpa only [hu,hv,hs (σ v) (σ u)] using hn

theorem colors_mem_of_root_of_nonzero (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (M : Matrix C C K) (hs : ∀ i j,M i j=M j i) (w : C → K)
    (X : Set C) (hX : ColorClosed M X) (σ : Fin g.vertices → C)
    (hr : σ r ∈ X) (h : (g.toMultiGraph hg).assignmentWeight M w σ ≠ 0) :
    ∀ v,σ v ∈ X := by
  intro v
  have hv := (SimpleGraph.reachable_iff_reflTransGen r v).mp (hc.preconnected r v)
  induction hv with
  | refl => exact hr
  | @tail u v _ huv ih => exact hX _ ih _ (assignment_adj_ne_zero g hg M hs w σ h u v huv)

/-- The literal color-submatrix partition value equals the single-root sum. -/
theorem rootRestricted_eq_submatrix (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (M : Matrix C C K) (hs : ∀ i j,M i j=M j i) (w : C → K)
    (X : Set C) (hX : ColorClosed M X) :
    (g.toMultiGraph hg).rootRestricted r M w X =
      (g.toMultiGraph hg).partition (fun i j : X => M i.val j.val) (fun i : X => w i.val) := by
  let G := g.toMultiGraph hg
  let P : (Fin g.vertices → C) → Prop := fun σ => ∀ v,σ v ∈ X
  have hbad : ∀ σ : {σ : Fin g.vertices → C // ¬ P σ},
      (if σ.val r ∈ X then G.assignmentWeight M w σ.val else 0)=0 := by
    intro σ
    by_cases hr : σ.val r ∈ X
    · simp only [hr,ite_true]
      by_contra hn
      exact σ.property (colors_mem_of_root_of_nonzero g hg hc r M hs w X hX σ.val hr hn)
    · simp [hr]
  unfold MultiGraph.rootRestricted MultiGraph.partition
  rw [← Fintype.sum_subtype_add_sum_subtype P
    (fun σ => if σ r ∈ X then G.assignmentWeight M w σ else 0)]
  simp only [hbad,Finset.sum_const_zero,add_zero]
  apply Fintype.sum_equiv (Equiv.subtypePiEquivPi (p := fun (_ : Fin g.vertices) i => i ∈ X))
  intro σ
  have hr := σ.property r
  simp only [hr,ite_true]
  rfl

/-- The usual loopless numerical support of the source matrix. -/
def colorSupport (M : Matrix C C K) (hs : ∀ i j,M i j=M j i) : SimpleGraph C where
  Adj i j := i ≠ j ∧ M i j ≠ 0
  symm := by intro i j h; exact ⟨h.1.symm,by simpa only [hs j i] using h.2⟩
  loopless := by intro i h; exact h.1 rfl

omit [Fintype C] in
theorem component_colorClosed (M : Matrix C C K) (hs : ∀ i j,M i j=M j i)
    (c : (colorSupport M hs).ConnectedComponent) : ColorClosed M c.supp := by
  intro i hi j hij
  by_cases he : i=j
  · simpa only [← he] using hi
  · exact c.mem_supp_of_adj_mem_supp hi ⟨he,hij⟩

end PlanarHom.RootedRestriction
