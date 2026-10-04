import PlanarHom.RadialPottsAssemblyDegrees
import PlanarHom.PottsCenteredLeafCancellation

/-! NEW reconstruction: selected degrees and cardinalities of the actual
assembly split into its complete long set and the literal short selections
inside each tile. This retains occurrences on loops and parallel source edges. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile
variable {E : Type} [Fintype E] {k : ℕ}

def shortAt (A : Finset (E × RadialPottsTile.Edge k)) (e : E) : Finset (HalfShort k × Bool) :=
  Finset.univ.filter (fun f => (e,.inr f)∈A)

@[simp] theorem mem_shortAt (A : Finset (E × RadialPottsTile.Edge k)) (e : E) (f : HalfShort k × Bool) :
    f∈shortAt A e ↔ (e,.inr f)∈A := by simp [shortAt]

@[simp] theorem longEdges_mem_left (e : E) (f : Long k) : (e,.inl f)∈longEdges E k := by
  letI : DecidableEq (E × RadialPottsTile.Edge k) := Classical.decEq _
  apply Finset.mem_image.mpr
  exact ⟨(e,f),Finset.mem_univ _,rfl⟩

@[simp] theorem longEdges_not_mem_right (e : E) (f : HalfShort k × Bool) : (e,.inr f)∉longEdges E k := by
  letI : DecidableEq (E × RadialPottsTile.Edge k) := Classical.decEq _
  intro h
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp h
  exact Sum.noConfusion (congrArg (fun p : E × RadialPottsTile.Edge k => p.2) ha)

private theorem degree_sum {W F : Type} [Fintype F] (G : MultiGraph W F) (A : Finset F) (v : W) :
    G.selectedDegree A v=∑ e : F,if e∈A then G.endpointCount e v else 0 := by
  rw [← Finset.sum_filter]
  simp [selectedDegree_eq_sum_endpointCount]

def shortContribution (rotation : Equiv.Perm (Medial.Dart E))
    (A : Finset (E × RadialPottsTile.Edge k)) (v : Vertex E k) (e : E) : ℕ :=
  ∑ f : HalfShort k × Bool,if (e,.inr f)∈A then (graph rotation k).endpointCount (e,.inr f) v else 0

theorem selection_degree_split (rotation : Equiv.Perm (Medial.Dart E))
    (A : Finset (E × RadialPottsTile.Edge k)) (hA : longEdges E k⊆A) (v : Vertex E k) :
    (graph rotation k).selectedDegree A v=
      (longGraph rotation k).selectedDegree Finset.univ v+∑ e,shortContribution rotation A v e := by
  rw [degree_sum,degree_sum]
  simp only [Finset.mem_univ,ite_true]
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sum_type]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    rw [if_pos (hA (longEdges_mem_left e f))]
    rfl
  · apply Finset.sum_congr rfl
    intro e _
    unfold shortContribution
    apply Finset.sum_congr rfl
    intro f _
    by_cases h : (e,Sum.inr f)∈A <;> simp [h]

theorem shortContribution_white (rotation : Equiv.Perm (Medial.Dart E))
    (A : Finset (E × RadialPottsTile.Edge k)) (e : E) (w : White k) :
    (∑ a,shortContribution rotation A (.inl (e,w)) a)=
      (shortGraph k).selectedDegree (shortAt A e) w := by
  rw [Finset.sum_eq_single e]
  · rw [degree_sum]
    apply Finset.sum_congr rfl
    intro f _
    simp [endpointCount,graph,embed,RadialPottsTile.graph,shortGraph,shortAt]
    split_ifs <;> rfl
  · intro a _ ha
    simp [shortContribution,endpointCount,graph,embed,RadialPottsTile.graph,ha]
  · simp

theorem shortContribution_port (rotation : Equiv.Perm (Medial.Dart E))
    (A : Finset (E × RadialPottsTile.Edge k)) (w : Medial.Dart E × Fin k) :
    (∑ a,shortContribution rotation A (.inr w) a)=0 := by
  simp [shortContribution,endpointCount,graph,embed,RadialPottsTile.graph]

theorem selectedDegree_white (rotation : Equiv.Perm (Medial.Dart E))
    (A : Finset (E × RadialPottsTile.Edge k)) (hA : longEdges E k⊆A) (e : E) (w : White k) :
    (graph rotation k).selectedDegree A (.inl (e,w))=
      1+(shortGraph k).selectedDegree (shortAt A e) w := by
  rw [selection_degree_split rotation A hA,long_degree,shortContribution_white]

theorem selectedDegree_port (rotation : Equiv.Perm (Medial.Dart E))
    (A : Finset (E × RadialPottsTile.Edge k)) (hA : longEdges E k⊆A) (w : Medial.Dart E × Fin k) :
    (graph rotation k).selectedDegree A (.inr w)=2 := by
  rw [selection_degree_split rotation A hA,long_degree,shortContribution_port]

theorem short_card_sum (A : Finset (E × RadialPottsTile.Edge k)) :
    ∑ e : E,(shortAt A e).card=(A\longEdges E k).card := by
  have hc : (A\longEdges E k).card=
      ∑ p : E × RadialPottsTile.Edge k,if p∈A\longEdges E k then 1 else 0 := by
    symm
    exact (@Finset.sum_boole (E × RadialPottsTile.Edge k) ℕ _ (fun p => p∈A\longEdges E k)
      (fun p => Finset.decidableMem p (A\longEdges E k)) Finset.univ).trans (congrArg Finset.card (show _ = A\longEdges E k from by ext p; simp))
  rw [hc,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.sum_sum_type]
  simp only [Finset.mem_sdiff,longEdges_mem_left,not_true_eq_false,and_false,ite_false,
    Finset.sum_const_zero,zero_add,longEdges_not_mem_right,not_false_eq_true,and_true]
  symm
  exact (@Finset.sum_boole (HalfShort k × Bool) ℕ _ (fun f => (e,Sum.inr f)∈A)
    (fun f => Finset.decidableMem (e,Sum.inr f) A) Finset.univ).trans
      (congrArg Finset.card (show _ = shortAt A e from by ext f; simp [shortAt]))
end PlanarHom.RadialPotts.Assembly
