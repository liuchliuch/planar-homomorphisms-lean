import PlanarHom.RadialPottsCoefficientStates
import PlanarHom.PottsMarkedCoefficientFilter

/-! NEW reconstruction: the actual marked coefficient is exactly the sum over
Boolean tile states. Zero-weight nonstates are eliminated by proved cancellation;
the state map is injective for k>0, so no multiplicity is silently introduced. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile PottsCentered
variable {E : Type} [Fintype E] {k : ℕ}

def filteredStateSum (rotation : Equiv.Perm (Medial.Dart E)) (q k : ℕ) : ℚ :=
  ∑ A : Finset (E × RadialPottsTile.Edge k),
    if longEdges E k⊆A ∧ (A\longEdges E k).card=2*k^2*Fintype.card E
    then selectedValue (graph rotation k) q A else 0

theorem filteredStateSum_eq (rotation : Equiv.Perm (Medial.Dart E))
    (q : ℕ) (hq : 0<q) (hk : 0<k) :
    filteredStateSum rotation q k=
      ∑ choice : E → Bool,selectedValue (graph rotation k) q (stateEdges choice) := by
  letI : DecidableEq (Finset (E × RadialPottsTile.Edge k)) := Classical.decEq _
  let f : Finset (E × RadialPottsTile.Edge k) → ℚ := fun A =>
    if longEdges E k⊆A ∧ (A\longEdges E k).card=2*k^2*Fintype.card E
    then selectedValue (graph rotation k) q A else 0
  let states := Finset.univ.image (stateEdges (E:=E) (k:=k))
  have hs (A : Finset (E × RadialPottsTile.Edge k)) (hn : f A≠0) : A∈states := by
    dsimp [f] at hn
    split_ifs at hn with h
    · obtain ⟨choice,rfl⟩ := nonzero_is_state rotation q hq A h.1 h.2 hn
      exact Finset.mem_image.mpr ⟨choice,Finset.mem_univ _,rfl⟩
    · exact (hn rfl).elim
  have hz (A : Finset (E × RadialPottsTile.Edge k)) (_ : A∈Finset.univ) (ha : A∉states) : f A=0 := by
    by_contra hn
    exact ha (hs A hn)
  have hf (choice : E → Bool) : f (stateEdges choice)=selectedValue (graph rotation k) q (stateEdges choice) := by
    exact if_pos ⟨state_long_subset choice,state_short_card choice⟩
  calc
    _ = ∑ A∈states,f A := (Finset.sum_subset (Finset.subset_univ states) hz).symm
    _ = ∑ choice : E → Bool,f (stateEdges choice) := Finset.sum_image (stateEdges_injective hk).injOn
    _ = _ := Finset.sum_congr rfl (fun choice _ => hf choice)

theorem marked_coefficient_eq_filtered (rotation : Equiv.Perm (Medial.Dart E)) (q N : ℕ)
    (hN : (Finset.univ\longEdges E k).card<N) :
    (markedPolynomial (graph rotation k) q (longEdges E k) N).coeff
      (N*(longEdges E k).card+2*k^2*Fintype.card E)=filteredStateSum rotation q k := by
  unfold filteredStateSum
  have hi : (inferInstance : DecidableEq (E × RadialPottsTile.Edge k))=
      Classical.decEq (E × RadialPottsTile.Edge k) := Subsingleton.elim _ _
  dsimp only [inferInstance] at hi
  rw [hi] at hN ⊢
  exact marked_coefficient_filter (graph rotation k) q (longEdges E k) N
    (2*k^2*Fintype.card E) hN

/-- The surviving coefficient is a sum of actual normalized selected graph
partition functions, one per Boolean state on the original edge occurrences. -/
theorem marked_coefficient_eq_stateSum (rotation : Equiv.Perm (Medial.Dart E))
    (q N : ℕ) (hq : 0<q) (hk : 0<k) (hN : (Finset.univ\longEdges E k).card<N) :
    (markedPolynomial (graph rotation k) q (longEdges E k) N).coeff
      (N*(longEdges E k).card+2*k^2*Fintype.card E)=
      ∑ choice : E → Bool,selectedValue (graph rotation k) q (stateEdges choice) := by
  rw [marked_coefficient_eq_filtered rotation q N hN,filteredStateSum_eq rotation q hq hk]
end PlanarHom.RadialPotts.Assembly
