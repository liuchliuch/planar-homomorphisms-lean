import PlanarHom.RadialPottsOnionBoundaryAtlas

/-! Component labels are constant on the actual long and unswitched red edge
occurrences. Together with the atlas path steps this identifies components. -/
namespace PlanarHom.RadialPottsTile.OnionBoundary

private theorem longLeft_eq {k : ℕ} (e : Long k) :
    longLeft e=whiteAt e.1 e.2.1 (2*e.2.2.val) (by have := e.2.2.isLt; omega) := rfl

/-- The literal long matching preserves the onion path label. -/
theorem component_long {k : ℕ} (e : Long k) :
    component (.inl (longLeft e))=component (longRight e) := by
  rw [longLeft_eq]
  by_cases h : e.1.val+1<k
  · have hr : longRight e= .inl (whiteAt ⟨e.1.val+1,h⟩ e.2.1
        (2*e.2.2.val+1) (by dsimp; have := e.2.2.isLt; omega)) := by
      rw [longRight,dif_pos h]
      rfl
    rw [hr]
    simp only [component,side_whiteAt,offset_whiteAt]
    apply Prod.ext
    · rfl
    · split <;> apply Fin.ext <;> dsimp [whiteAt] <;> omega
  · rw [longRight,dif_neg h]
    simp only [component,side_whiteAt,offset_whiteAt]
    apply Prod.ext
    · rfl
    · split <;> apply Fin.ext <;> dsimp [whiteAt]
      · omega
      · have := e.1.isLt
        omega


private theorem component_red_inner {k : ℕ} (r : Fin k) (s : Fin 4)
    (t : ℕ) (ht : t<2*r.val) (hp : (s.val+t)%2=0) :
    component (.inl (whiteAt r s t (by omega)))=
      component (.inl (whiteAt r s (t+1) (by omega))) := by
  simp only [component,side_whiteAt,offset_whiteAt]
  apply Prod.ext
  · rfl
  · split <;> apply Fin.ext <;> dsimp [whiteAt] <;> omega

private theorem component_red_corner {k : ℕ} (r : Fin k) (s : Fin 4)
    (hs : s.val%2=0) :
    component (.inl (whiteAt r s (2*r.val) (by omega)))=
      component (.inl (whiteAt r ⟨s.val+1,by have := s.isLt; omega⟩ 0 (by omega))) := by
  simp only [component,side_whiteAt,offset_whiteAt]
  rw [if_pos hs,if_neg (show (s.val+1)%2≠0 by omega)]
  apply Prod.ext <;> apply Fin.ext <;> dsimp [whiteAt] <;> omega

/-- Every unswitched red short edge preserves the onion path label. -/
theorem component_red {k : ℕ} (e : HalfShort k) :
    component (.inl (evenWhite e))=component (.inl (oddWhite e)) := by
  let s := side (evenWhite e)
  let t := offset (evenWhite e)
  have ht : t≤2*e.1.val := offset_le (evenWhite e)
  have hev : evenWhite e=whiteAt e.1 s t ht := (whiteAt_side_offset _).symm
  have hsum : s.val*(2*e.1.val+1)+t=2*e.2.val := by
    have hh := congrArg (fun w : White k => w.2.val) hev
    exact hh.symm
  have hp : (s.val+t)%2=0 := by
    have hh := congrArg (fun n : ℕ => n%2) hsum
    simpa [Nat.add_mod,Nat.mul_mod] using hh
  by_cases hlt : t<2*e.1.val
  · have hod : oddWhite e=whiteAt e.1 s (t+1) (by omega) := by
      apply white_ext
      · rfl
      · dsimp [oddWhite,whiteAt]
        omega
    rw [hev,hod]
    exact component_red_inner e.1 s t hlt hp
  · have heq : t=2*e.1.val := by omega
    have hs : s.val%2=0 := by omega
    have hod : oddWhite e=whiteAt e.1 ⟨s.val+1,by have := s.isLt; omega⟩
        0 (by omega) := by
      apply white_ext
      · rfl
      · dsimp [oddWhite,whiteAt]
        rw [Nat.add_mul]
        omega
    rw [hev,hod]
    simpa only [heq] using component_red_corner e.1 s hs

end PlanarHom.RadialPottsTile.OnionBoundary
