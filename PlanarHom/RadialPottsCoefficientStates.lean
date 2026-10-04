import PlanarHom.RadialPottsAssemblySelections

/-! NEW reconstruction: every nonzero term surviving the actual long-edge
coefficient filter is one independently chosen red/blue state per source tile.
The converse states have the exact required occurrence count and degree two. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile PottsCentered
variable {E : Type} [Fintype E] {k : ℕ}

def stateEdges (choice : E → Bool) : Finset (E × RadialPottsTile.Edge k) :=
  Finset.univ.filter (fun p => match p.2 with | .inl _ => True | .inr f => f.2=choice p.1)

theorem state_long_subset (choice : E → Bool) : longEdges E k⊆stateEdges (k:=k) choice := by
  rintro ⟨e,f | f⟩ h
  · simp [stateEdges]
  · exact (longEdges_not_mem_right e f h).elim

@[simp] theorem shortAt_state (choice : E → Bool) (e : E) :
    shortAt (stateEdges (k:=k) choice) e=shortsOfColor k (choice e) := by
  ext f
  simp [shortAt,stateEdges,shortsOfColor]

theorem state_white_degree (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool)
    (e : E) (w : White k) : (graph rotation k).selectedDegree (stateEdges choice) (.inl (e,w))=2 := by
  rw [selectedDegree_white rotation _ (state_long_subset choice),shortAt_state,
    shortsOfColor_matching]

theorem state_port_degree (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool)
    (w : Medial.Dart E × Fin k) : (graph rotation k).selectedDegree (stateEdges choice) (.inr w)=2 :=
  selectedDegree_port rotation _ (state_long_subset choice) w

theorem shortsOfColor_card (c : Bool) : (shortsOfColor k c).card=2*k^2 := by
  have h := (shortsOfColor_matching k c).card_vertices (shortGraph k) (shortsOfColor k c)
  rw [card_white] at h
  omega

theorem state_short_card (choice : E → Bool) :
    (stateEdges (k:=k) choice\longEdges E k).card=2*k^2*Fintype.card E := by
  rw [← short_card_sum]
  simp only [shortAt_state,shortsOfColor_card,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  simp [Nat.cast_id,mul_assoc,mul_comm,mul_left_comm]

theorem stateEdges_injective (hk : 0<k) : Function.Injective (@stateEdges E _ k) := by
  intro a b h
  funext e
  let f : HalfShort k := ⟨⟨0,hk⟩,⟨0,by omega⟩⟩
  have hh := congrArg (fun A : Finset (E × RadialPottsTile.Edge k) => (e,.inr (f,false))∈A) h
  cases ha : a e <;> cases hb : b e <;> simp [stateEdges,ha,hb] at hh ⊢

theorem state_eq_of_shortAt (A : Finset (E × RadialPottsTile.Edge k))
    (hA : longEdges E k⊆A) (choice : E → Bool)
    (hs : ∀ e,shortAt A e=shortsOfColor k (choice e)) : A=stateEdges choice := by
  ext p
  rcases p with ⟨e,f | f⟩
  · simp [stateEdges,hA (longEdges_mem_left e f)]
  · rw [← mem_shortAt A e f,hs]
    simp [shortsOfColor,stateEdges]

/-- Degree-one cancellation and the exact edge count force degree one in each
short graph. No degree-two or tile-state property is an input assumption. -/
theorem nonzero_short_matchings (rotation : Equiv.Perm (Medial.Dart E))
    (q : ℕ) (hq : 0<q) (A : Finset (E × RadialPottsTile.Edge k))
    (hA : longEdges E k⊆A) (hc : (A\longEdges E k).card=2*k^2*Fintype.card E)
    (hn : selectedValue (graph rotation k) q A≠0) :
    ∀ e,(shortGraph k).PerfectMatching (shortAt A e) := by
  let f : E × White k → ℕ := fun p => (shortGraph k).selectedDegree (shortAt A p.1) p.2
  have hlo (p : E × White k) : 1≤f p := by
    by_contra h
    have hz : f p=0 := by omega
    have hd : (graph rotation k).selectedDegree A (.inl p)=1 := by
      rw [selectedDegree_white rotation A hA]
      change 1+f p=1
      rw [hz]
    exact hn (selectedValue_eq_zero_of_degree_one _ q hq A (.inl p) hd)
  have hsum : (∑ p : E × White k,f p)=Fintype.card (E × White k) := by
    rw [Fintype.sum_prod_type]
    simp only [f,(shortGraph k).sum_selectedDegree]
    rw [← Finset.mul_sum,short_card_sum,hc,Fintype.card_prod,card_white]
    ring
  have heq : (∑ p : E × White k,(1:ℕ))=∑ p,f p := by simpa using hsum.symm
  have hall := (Finset.sum_eq_sum_iff_of_le (fun p (_ : p∈(Finset.univ : Finset (E × White k))) => hlo p)).mp heq
  intro e w
  exact (hall (e,w) (Finset.mem_univ _)).symm

/-- Exact support of the genuine coefficient sum: every nonzero surviving
occurrence set comes from an actual Boolean state assignment to the tiles. -/
theorem nonzero_is_state (rotation : Equiv.Perm (Medial.Dart E))
    (q : ℕ) (hq : 0<q) (A : Finset (E × RadialPottsTile.Edge k))
    (hA : longEdges E k⊆A) (hc : (A\longEdges E k).card=2*k^2*Fintype.card E)
    (hn : selectedValue (graph rotation k) q A≠0) :
    ∃ choice : E → Bool,A=stateEdges choice := by
  have hm := nonzero_short_matchings rotation q hq A hA hc hn
  have he : ∀ e,∃ c : Bool,shortAt A e=shortsOfColor k c := by
    intro e
    rcases (short_matching_iff k (shortAt A e)).mp (hm e) with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  choose choice hchoice using he
  exact ⟨choice,state_eq_of_shortAt A hA choice hchoice⟩
end PlanarHom.RadialPotts.Assembly
