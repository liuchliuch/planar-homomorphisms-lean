import PlanarHom.RadialPottsTile
import PlanarHom.PottsRandomCluster

/-! NEW reconstruction: all switched short occurrences form one connected
cycle. Connectivity is proved on the literal onion endpoints: each cut ring is
a path, the switched red edges join rings two apart, and one joins rings 0,1. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPottsTile
open MultiGraph

def shortGraph (k : ℕ) : MultiGraph (White k) (HalfShort k × Bool) where
  src e := if e.2 then oddWhite e.1 else switch (evenWhite e.1)
  dst e := if e.2 then nextWhite e.1 else switch (oddWhite e.1)

abbrev ShortReach {k : ℕ} (u v : White k) : Prop :=
  (shortGraph k).componentSetoid Finset.univ u v

def atIndex {k : ℕ} (r : Fin k) (i : ℕ) (hi : i<8*r.val+4) : White k := ⟨r,⟨i,hi⟩⟩

private theorem red_reach {k : ℕ} (e : HalfShort k) :
    ShortReach (switch (evenWhite e)) (switch (oddWhite e)) :=
  Relation.EqvGen.rel _ _ ⟨(e,false),Finset.mem_univ _,rfl,rfl⟩

private theorem blue_reach {k : ℕ} (e : HalfShort k) :
    ShortReach (oddWhite e) (nextWhite e) :=
  Relation.EqvGen.rel _ _ ⟨(e,true),Finset.mem_univ _,rfl,rfl⟩

private theorem switch_atIndex {k : ℕ} (r : Fin k) (i : ℕ) (hi : i<8*r.val+4)
    (h0 : i≠0) (h1 : i≠1) : switch (atIndex r i hi)=atIndex r i hi := by
  simp [switch,atIndex,h0,h1]

/-- Consecutive ring positions from 1 onward are joined by their actual short
occurrence. The one omitted 0--1 edge is precisely the switched red edge. -/
theorem short_step {k : ℕ} (r : Fin k) (i : ℕ) (h1 : 1≤i) (hi : i+1<8*r.val+4) :
    ShortReach (atIndex r i (by omega)) (atIndex r (i+1) hi) := by
  let e : HalfShort k := ⟨r,⟨i/2,by omega⟩⟩
  rcases Nat.mod_two_eq_zero_or_one i with he | he
  · have hv : 2*(i/2)=i := by omega
    have hl : evenWhite e=atIndex r i (by omega) := by apply white_ext <;> simp [e,evenWhite,atIndex,hv]
    have hr : oddWhite e=atIndex r (i+1) hi := by apply white_ext <;> simp [e,oddWhite,atIndex,hv]
    have h := red_reach e
    rw [hl,hr,switch_atIndex r i _ (by omega) (by omega),
      switch_atIndex r (i+1) hi (by omega) (by omega)] at h
    exact h
  · have hv : 2*(i/2)+1=i := by omega
    have hl : oddWhite e=atIndex r i (by omega) := by apply white_ext <;> simp [e,oddWhite,atIndex,hv]
    have hr : nextWhite e=atIndex r (i+1) hi := by
      apply white_ext
      · rfl
      · change (2*(i/2)+2)%(8*r.val+4)=i+1
        have hh : 2*(i/2)+2=i+1 := by omega
        rw [hh,Nat.mod_eq_of_lt hi]
    simpa only [hl,hr] using blue_reach e

theorem short_last_zero {k : ℕ} (r : Fin k) :
    ShortReach (atIndex r (8*r.val+3) (by omega)) (atIndex r 0 (by omega)) := by
  let e : HalfShort k := ⟨r,⟨4*r.val+1,by omega⟩⟩
  have hl : oddWhite e=atIndex r (8*r.val+3) (by omega) := by
    apply white_ext
    · rfl
    · change 2*(4*r.val+1)+1=8*r.val+3
      omega
  have hr : nextWhite e=atIndex r 0 (by omega) := by
    apply white_ext
    · rfl
    · change (2*(4*r.val+1)+2)%(8*r.val+4)=0
      have h : 2*(4*r.val+1)+2=8*r.val+4 := by omega
      rw [h,Nat.mod_self]
  simpa only [hl,hr] using blue_reach e

private theorem one_to_positive {k : ℕ} (r : Fin k) (i : ℕ) (h1 : 1≤i)
    (hi : i<8*r.val+4) : ShortReach (atIndex r 1 (by omega)) (atIndex r i hi) := by
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases hz : i=0
    · subst i
      exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.trans _ _ _ (ih (by omega) (by omega)) (short_step r i (by omega) hi)

theorem short_ring_connected {k : ℕ} (r : Fin k) (i j : Fin (8*r.val+4)) :
    ShortReach (⟨r,i⟩ : White k) ⟨r,j⟩ := by
  have hone (a : Fin (8*r.val+4)) : ShortReach (atIndex r 1 (by omega)) ⟨r,a⟩ := by
    by_cases ha : a.val=0
    · have hh := Relation.EqvGen.trans _ _ _
        (one_to_positive r (8*r.val+3) (by omega) (by omega)) (short_last_zero r)
      simpa only [atIndex,show a=⟨0,by omega⟩ from Fin.ext ha] using hh
    · exact one_to_positive r a.val (by omega) a.isLt
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hone i)) (hone j)

private theorem short_two_rings {k : ℕ} (r : ℕ) (hr : r+2<k) :
    ShortReach (atIndex ⟨r,by omega⟩ 0 (by omega))
      (atIndex ⟨r+2,hr⟩ 0 (by omega)) := by
  let e : HalfShort k := ⟨⟨r+1,by omega⟩,⟨0,by omega⟩⟩
  have hl : switch (evenWhite e)=atIndex ⟨r+2,hr⟩ 1 (by omega) := by
    dsimp [e,evenWhite]
    rw [switch,dif_pos (by dsimp; omega)]
    apply white_ext <;> simp [atIndex]
  have hd : switch (oddWhite e)=atIndex ⟨r,by omega⟩ 0 (by omega) := by
    dsimp [e,oddWhite]
    rw [switch,dif_neg (by simp [Nat.mod_eq_of_lt (show 1<8*(r+1)+4 by omega)]),
      dif_pos (by simp [Nat.mod_eq_of_lt (show 1<8*(r+1)+4 by omega)])]
    apply white_ext <;> simp [atIndex]
  have hh := red_reach e
  rw [hl,hd] at hh
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hh)
    (short_ring_connected ⟨r+2,hr⟩ ⟨1,by omega⟩ ⟨0,by omega⟩)

private theorem short_first_rings {k : ℕ} (hk : 1<k) :
    ShortReach (atIndex ⟨0,by omega⟩ 0 (by omega))
      (atIndex ⟨1,hk⟩ 0 (by omega)) := by
  let e : HalfShort k := ⟨⟨0,by omega⟩,⟨0,by omega⟩⟩
  have hl : switch (evenWhite e)=atIndex ⟨1,hk⟩ 1 (by omega) := by
    dsimp [e,evenWhite]
    rw [switch,dif_pos (by dsimp; omega)]
    apply white_ext <;> simp [atIndex]
  have hd : switch (oddWhite e)=atIndex ⟨0,by omega⟩ 1 (by omega) := by
    apply white_ext <;> simp [e,oddWhite,switch,atIndex]
  have hh := red_reach e
  rw [hl,hd] at hh
  exact Relation.EqvGen.trans _ _ _ (short_ring_connected ⟨0,by omega⟩ ⟨0,by omega⟩ ⟨1,by omega⟩)
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hh)
      (short_ring_connected ⟨1,hk⟩ ⟨1,by omega⟩ ⟨0,by omega⟩))

/-- Every two actual white vertices are joined by selected short occurrences. -/
theorem short_connected {k : ℕ} (u v : White k) : ShortReach u v := by
  have hk : 0<k := by have := u.1.isLt; omega
  have hr (r : ℕ) (h : r<k) :
      ShortReach (atIndex ⟨0,hk⟩ 0 (by omega)) (atIndex ⟨r,h⟩ 0 (by omega)) := by
    induction r using Nat.strong_induction_on with
    | h r ih =>
      rcases r with _ | r
      · exact Relation.EqvGen.refl _
      rcases r with _ | r
      · exact short_first_rings h
      · exact Relation.EqvGen.trans _ _ _ (ih r (by omega) (by omega)) (short_two_rings r h)
  have hu := short_ring_connected u.1 u.2 ⟨0,by omega⟩
  have hv := short_ring_connected v.1 ⟨0,by omega⟩ v.2
  exact Relation.EqvGen.trans _ _ _ hu (Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (hr u.1.val u.1.isLt)) (Relation.EqvGen.trans _ _ _ (hr v.1.val v.1.isLt) hv))
end PlanarHom.RadialPottsTile
