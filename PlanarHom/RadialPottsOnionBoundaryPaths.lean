import PlanarHom.RadialPottsOnionGraphs

/-! NEW reconstruction: actual red-onion paths climb to their stated boundary
ports. The paths are proved from the literal long/red occurrences; no boundary
connectivity or hidden-component premise is introduced. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPottsTile.OnionBoundary
open MultiGraph

abbrev RedReach {k : ℕ} (u v : Vertex k) := (redGraph k).componentSetoid Finset.univ u v

private theorem reach_long {k : ℕ} (e : Long k) : RedReach (.inl (longLeft e)) (longRight e) :=
  Relation.EqvGen.rel _ _ ⟨.inl e,Finset.mem_univ _,rfl,rfl⟩

private theorem reach_short {k : ℕ} (e : HalfShort k) :
    RedReach (.inl (evenWhite e)) (.inl (oddWhite e)) :=
  Relation.EqvGen.rel _ _ ⟨.inr e,Finset.mem_univ _,rfl,rfl⟩

/-- A side-local red edge, with the exact alternating parity. -/
theorem reach_red_inner {k : ℕ} (r : Fin k) (s : Fin 4) (t : ℕ)
    (ht : t<2*r.val) (hp : (s.val+t)%2=0) :
    RedReach (.inl (whiteAt r s t (by omega))) (.inl (whiteAt r s (t+1) (by omega))) := by
  let m := s.val*(2*r.val+1)+t
  have hm : m<8*r.val+4 := (whiteAt r s t (by omega)).2.isLt
  have hmod : m%2=0 := by
    dsimp [m]
    simpa [Nat.add_mod,Nat.mul_mod] using hp
  let e : HalfShort k := ⟨r,⟨m/2,by omega⟩⟩
  have hs : evenWhite e=whiteAt r s t (by omega) := by
    apply white_ext
    · rfl
    · change 2*(m/2)=m
      omega
  have hd : oddWhite e=whiteAt r s (t+1) (by omega) := by
    apply white_ext
    · rfl
    · change 2*(m/2)+1=s.val*(2*r.val+1)+(t+1)
      change 2*(m/2)+1=m+1
      omega
  rw [← hs,← hd]
  exact reach_short e

/-- The bottom turn connects the two sides of each red path family. -/
theorem reach_red_corner {k : ℕ} (r : Fin k) (s : Fin 4) (hp : s.val%2=0) :
    RedReach (.inl (whiteAt r s (2*r.val) (by omega)))
      (.inl (whiteAt r ⟨s.val+1,by have := s.isLt; omega⟩ 0 (by omega))) := by
  let m := s.val*(2*r.val+1)+2*r.val
  have hm : m<8*r.val+4 := (whiteAt r s (2*r.val) (by omega)).2.isLt
  have hmod : m%2=0 := by simp [m,Nat.add_mod,Nat.mul_mod,hp]
  let e : HalfShort k := ⟨r,⟨m/2,by omega⟩⟩
  have hs : evenWhite e=whiteAt r s (2*r.val) (by omega) := by
    apply white_ext
    · rfl
    · change 2*(m/2)=m
      omega
  have hd : oddWhite e=whiteAt r ⟨s.val+1,by have := s.isLt; omega⟩ 0 (by omega) := by
    apply white_ext
    · rfl
    · change 2*(m/2)+1=(s.val+1)*(2*r.val+1)+0
      have he : 2*(m/2)=m := by omega
      rw [he]
      dsimp [m]
      ring
  rw [← hs,← hd]
  exact reach_short e

def outerLane {k : ℕ} (r : Fin k) (s : Fin 4) (a : ℕ) (ha : a≤r.val) : Fin k :=
  ⟨if s.val%2=0 then a else k-1-r.val+a,by split_ifs <;> have := r.isLt <;> omega⟩

/-- Starting at any even local offset, actual alternating long/red steps reach
the outer boundary. Odd sides increase their offset at each outward step. -/
theorem evenOffset_to_port {k : ℕ} (r : Fin k) (s : Fin 4) (a : ℕ) (ha : a≤r.val) :
    RedReach (.inl (whiteAt r s (2*a) (by omega))) (.inr (s,outerLane r s a ha)) := by
  have aux : ∀ d : ℕ,∀ r : Fin k,k-1-r.val=d → ∀ a : ℕ,∀ ha : a≤r.val,
      RedReach (.inl (whiteAt r s (2*a) (by omega))) (.inr (s,outerLane r s a ha)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro r hd a ha
      let e : Long k := ⟨r,(s,⟨a,by omega⟩)⟩
      have hs : longLeft e=whiteAt r s (2*a) (by omega) := rfl
      by_cases hn : r.val+1<k
      · let r' : Fin k := ⟨r.val+1,hn⟩
        have hh : longRight e=.inl (whiteAt r' s (2*a+1) (by dsimp [r']; omega)) := by
          rw [longRight,dif_pos hn]
          rfl
        have hlong := reach_long e
        rw [hs,hh] at hlong
        have hd' : k-1-r'.val<d := by dsimp [r']; omega
        by_cases hp : s.val%2=0
        · have hred := reach_red_inner r' s (2*a) (by dsimp [r']; omega)
            (by simpa [Nat.add_mod,Nat.mul_mod] using hp)
          have hnext := ih _ hd' r' rfl a (by dsimp [r']; omega)
          have he : outerLane r' s a (by dsimp [r']; omega)=outerLane r s a ha := by
            apply Fin.ext
            simp [outerLane,hp]
          rw [he] at hnext
          exact Relation.EqvGen.trans _ _ _ hlong
            (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hred) hnext)
        · have hred := reach_red_inner r' s (2*a+1) (by dsimp [r']; omega) (by omega)
          have hnext := ih _ hd' r' rfl (a+1) (by dsimp [r']; omega)
          have hv : whiteAt r' s (2*a+1+1) (by dsimp [r']; omega)=
              whiteAt r' s (2*(a+1)) (by dsimp [r']; omega) := by
            apply whiteAt_ext <;> omega
          have he : outerLane r' s (a+1) (by dsimp [r']; omega)=outerLane r s a ha := by
            apply Fin.ext
            simp only [outerLane,if_neg hp]
            dsimp [r']
            omega
          rw [hv] at hred
          rw [he] at hnext
          exact Relation.EqvGen.trans _ _ _ hlong (Relation.EqvGen.trans _ _ _ hred hnext)
      · have hh : longRight e=.inr (s,outerLane r s a ha) := by
          rw [longRight,dif_neg hn]
          apply congrArg Sum.inr
          apply Prod.ext
          · rfl
          apply Fin.ext
          change a=(if s.val%2=0 then a else k-1-r.val+a)
          split_ifs <;> have := r.isLt <;> omega
        rw [← hs,← hh]
        exact reach_long e
  exact aux _ r rfl a ha

/-- Exact red terminal pairing, including reversed lane order. -/
theorem red_port_pair {k : ℕ} (c : Fin 2) (a : Fin k) :
    RedReach (.inr (⟨2*c.val,by have := c.isLt; omega⟩,a))
      (.inr (⟨2*c.val+1,by have := c.isLt; omega⟩,⟨k-1-a.val,by have := a.isLt; omega⟩)) := by
  let s : Fin 4 := ⟨2*c.val,by have := c.isLt; omega⟩
  have he := evenOffset_to_port a s a.val (by omega)
  have hc := reach_red_corner a s (by dsimp [s]; omega)
  have ho := evenOffset_to_port a ⟨s.val+1,by dsimp [s]; have := c.isLt; omega⟩ 0 (by omega)
  have hleft : outerLane a s a.val (by omega)=a := by
    apply Fin.ext
    simp [outerLane,s]
  have hright : outerLane a ⟨s.val+1,by dsimp [s]; have := c.isLt; omega⟩ 0 (by omega)=
      ⟨k-1-a.val,by have := a.isLt; omega⟩ := by
    apply Fin.ext
    simp [outerLane,s]
  rw [hleft] at he
  rw [hright] at ho
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ he)
    (Relation.EqvGen.trans _ _ _ hc ho)
end PlanarHom.RadialPottsTile.OnionBoundary
