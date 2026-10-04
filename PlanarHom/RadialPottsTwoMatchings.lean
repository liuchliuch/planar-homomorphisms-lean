import PlanarHom.RadialPottsShortEndpoints
import PlanarHom.FisherIncidenceOrdering

/-! NEW reconstruction: the literal switched short graph has precisely the
red and blue perfect matchings. The proof uses its actual degree and connected
endpoint graph, rather than an assumed tile truth table. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RadialPottsTile
open MultiGraph

private def shortDartEquiv (k : ℕ) : ((HalfShort k × Bool) × Bool) ≃ (Bool × White k) where
  toFun d := (d.1.2,shortEndpoint d.1.2 (d.1.1,d.2))
  invFun p := let e := (shortEndpointEquiv k p.1).symm p.2; ((e.1,p.1),e.2)
  left_inv d := by
    rcases d with ⟨⟨e,c⟩,b⟩
    change ((((shortEndpointEquiv k c).symm ((shortEndpointEquiv k c) (e,b))).1,c),
      ((shortEndpointEquiv k c).symm ((shortEndpointEquiv k c) (e,b))).2)=((e,c),b)
    simp
  right_inv p := by
    rcases p with ⟨c,w⟩
    change (c,(shortEndpointEquiv k c) ((shortEndpointEquiv k c).symm w))=(c,w)
    simp

private theorem dartVertex_eq {k : ℕ} (d : (HalfShort k × Bool) × Bool) :
    (shortGraph k).dartVertex d=shortEndpoint d.1.2 (d.1.1,d.2) := by
  rcases d with ⟨⟨e,c⟩,b⟩
  cases b <;> cases c <;> rfl

/-- There is one red and one blue endpoint at each white vertex. -/
theorem short_selectedDegree {k : ℕ} (S : Finset (HalfShort k × Bool)) (w : White k) :
    (shortGraph k).selectedDegree S w=
      (if (shortIndex false w,false)∈S then 1 else 0)+
      (if (shortIndex true w,true)∈S then 1 else 0) := by
  rw [selectedDegree_eq_dartCount,Fintype.card_subtype,Finset.card_filter]
  rw [Fintype.sum_equiv (shortDartEquiv k)
    (fun d => if d.1∈S ∧ (shortGraph k).dartVertex d=w then 1 else 0)
    (fun p => if (shortIndex p.1 p.2,p.1)∈S ∧ p.2=w then 1 else 0) (by
      intro d
      change (if d.1∈S ∧ (shortGraph k).dartVertex d=w then 1 else 0)=
        (if (shortIndex d.1.2 (shortEndpoint d.1.2 (d.1.1,d.2)),d.1.2)∈S ∧
          shortEndpoint d.1.2 (d.1.1,d.2)=w then 1 else 0)
      rw [shortIndex_endpoint,dartVertex_eq])]
  rw [Fintype.sum_prod_type]
  have hh (c : Bool) :
      (∑ v : White k,if (shortIndex c v,c)∈S ∧ v=w then 1 else 0 : ℕ)=
        if (shortIndex c w,c)∈S then 1 else 0 := by
    rw [Finset.sum_eq_single w]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  simp only [hh,Fintype.sum_bool]
  omega

def shortsOfColor (k : ℕ) (c : Bool) : Finset (HalfShort k × Bool) :=
  Finset.univ.filter (fun e => e.2=c)

theorem shortsOfColor_matching (k : ℕ) (c : Bool) :
    (shortGraph k).PerfectMatching (shortsOfColor k c) := by
  intro w
  rw [short_selectedDegree]
  cases c <;> simp [shortsOfColor]

private def redChosen {k : ℕ} (S : Finset (HalfShort k × Bool)) (w : White k) : Prop :=
  (shortIndex false w,false)∈S

private theorem chosen_edge {k : ℕ} {S : Finset (HalfShort k × Bool)}
    (hS : (shortGraph k).PerfectMatching S) (e : HalfShort k × Bool) :
    redChosen S ((shortGraph k).src e) ↔ redChosen S ((shortGraph k).dst e) := by
  rcases e with ⟨e,c⟩
  cases c
  · change redChosen S (shortEndpoint false (e,false)) ↔ redChosen S (shortEndpoint false (e,true))
    simp only [redChosen,shortIndex_endpoint]
  · have hs := hS ((shortGraph k).src (e,true))
    have hd := hS ((shortGraph k).dst (e,true))
    rw [short_selectedDegree] at hs hd
    have hi : shortIndex true ((shortGraph k).src (e,true))=e := shortIndex_endpoint true e false
    have hj : shortIndex true ((shortGraph k).dst (e,true))=e := shortIndex_endpoint true e true
    rw [hi] at hs
    rw [hj] at hd
    unfold redChosen
    split_ifs at hs hd <;> simp_all

private theorem chosen_reach {k : ℕ} {S : Finset (HalfShort k × Bool)}
    (hS : (shortGraph k).PerfectMatching S) {u v : White k} (h : ShortReach u v) :
    redChosen S u ↔ redChosen S v := by
  induction h with
  | rel u v h =>
    obtain ⟨e,_,rfl,rfl⟩ := h
    exact chosen_edge hS e
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ij => exact ih.trans ij

/-- The two actual short-color matchings exhaust every degree-one selection. -/
theorem short_matching_iff (k : ℕ) (S : Finset (HalfShort k × Bool)) :
    (shortGraph k).PerfectMatching S ↔ S=shortsOfColor k false ∨ S=shortsOfColor k true := by
  constructor
  · intro hS
    by_cases hk : k=0
    · subst k
      left
      ext e
      exact Fin.elim0 e.1.1
    · let w : White k := ⟨⟨0,by omega⟩,⟨0,by omega⟩⟩
      have hc (v : White k) : redChosen S v ↔ redChosen S w := chosen_reach hS (short_connected v w)
      by_cases hw : redChosen S w
      · left
        ext e
        rcases e with ⟨e,c⟩
        cases c
        · have h : redChosen S (shortEndpoint false (e,false)) := (hc _).mpr hw
          simpa [redChosen,shortIndex_endpoint,shortsOfColor] using h
        · have hd := hS (shortEndpoint true (e,false))
          rw [short_selectedDegree,shortIndex_endpoint] at hd
          have hr : redChosen S (shortEndpoint true (e,false)) := (hc _).mpr hw
          unfold redChosen at hr
          simp only [if_pos hr] at hd
          have hn : (e,true)∉S := by intro he; simp [he] at hd
          simp [shortsOfColor,hn]
      · right
        ext e
        rcases e with ⟨e,c⟩
        cases c
        · have hn : ¬redChosen S (shortEndpoint false (e,false)) := fun h => hw ((hc _).mp h)
          simpa [redChosen,shortIndex_endpoint,shortsOfColor] using hn
        · have hd := hS (shortEndpoint true (e,false))
          rw [short_selectedDegree,shortIndex_endpoint] at hd
          have hr : ¬redChosen S (shortEndpoint true (e,false)) := fun h => hw ((hc _).mp h)
          unfold redChosen at hr
          simp only [if_neg hr,zero_add] at hd
          have he : (e,true)∈S := by by_contra hn; simp [hn] at hd
          simp [shortsOfColor,he]
  · rintro (rfl | rfl) <;> exact shortsOfColor_matching _ _
end PlanarHom.RadialPottsTile
