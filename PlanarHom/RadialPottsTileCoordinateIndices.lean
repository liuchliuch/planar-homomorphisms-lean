import PlanarHom.RadialPottsTileCoordinates

/-! NEW exact quotient/remainder formulas for the ordered square-ring vertices. -/
namespace PlanarHom.RadialPottsTileCoordinates
open IntegerStraightDrawing RadialPottsTile

theorem white_point_of_index {k : ℕ} (w : White k) (s : Fin 4) (t : ℕ)
    (ht : t<2*w.1.val+1) (hi : w.2.val=s.val*(2*w.1.val+1)+t) :
    point (.inl w)=turn s ((t:ℤ)-(w.1.val:ℤ),(w.1.val:ℤ)+1) := by
  have hd : w.2.val/(2*w.1.val+1)=s.val := by
    rw [hi,Nat.mul_comm s.val,Nat.mul_add_div (by omega),Nat.div_eq_of_lt ht,Nat.add_zero]
  have hm : w.2.val%(2*w.1.val+1)=t := by
    rw [hi,Nat.mul_comm s.val,Nat.mul_add_mod,Nat.mod_eq_of_lt ht]
  have hs : whiteSide w=s := Fin.ext hd
  simp [point,hs,whiteOffset,hm]

theorem white_index_decomposition {k : ℕ} (w : White k) :
    w.2.val=(whiteSide w).val*(2*w.1.val+1)+w.2.val%(2*w.1.val+1) := by
  dsimp [whiteSide]
  simpa [Nat.mul_comm] using (Nat.div_add_mod w.2.val (2*w.1.val+1)).symm

def nextWhiteIndex {k : ℕ} (w : White k) : White k :=
  ⟨w.1,⟨(w.2.val+1)%(8*w.1.val+4),Nat.mod_lt _ (by omega)⟩⟩

theorem nextWhite_point_side {k : ℕ} (w : White k)
    (ht : w.2.val%(2*w.1.val+1)<2*w.1.val) :
    point (.inl (nextWhiteIndex w))=
      turn (whiteSide w) (((w.2.val%(2*w.1.val+1):ℕ):ℤ)+1-(w.1.val:ℤ),(w.1.val:ℤ)+1) := by
  have hdec:=white_index_decomposition w
  have hs: (whiteSide w).val≤3 := by have:=(whiteSide w).isLt; omega
  have hbound : w.2.val+1<8*w.1.val+4 := by
    have hh:=Nat.mul_le_mul_right (2*w.1.val+1) hs
    omega
  have hp := white_point_of_index (nextWhiteIndex w) (whiteSide w)
    (w.2.val%(2*w.1.val+1)+1) (by dsimp [nextWhiteIndex]; omega) (by
      dsimp [nextWhiteIndex]
      rw [Nat.mod_eq_of_lt hbound]
      omega)
  simpa only [nextWhiteIndex,Nat.cast_add,Nat.cast_one] using hp

theorem nextWhite_point_corner {k : ℕ} (w : White k)
    (ht : w.2.val%(2*w.1.val+1)=2*w.1.val) :
    point (.inl (nextWhiteIndex w))=turn (whiteSide w) ((w.1.val:ℤ)+1,w.1.val) := by
  have hdec:=white_index_decomposition w
  rw [ht] at hdec
  have hs := (whiteSide w).isLt
  generalize he : whiteSide w=s at *
  fin_cases s
  · have hi : w.2.val+1=2*w.1.val+1 := by simp at hdec; omega
    have hp := white_point_of_index (nextWhiteIndex w) 1 0 (by dsimp [nextWhiteIndex]; omega) (by
      dsimp [nextWhiteIndex]; rw [hi,Nat.mod_eq_of_lt (by omega)] <;> simp)
    simpa [turn,nextWhiteIndex] using hp
  · have hi : w.2.val+1=2*(2*w.1.val+1) := by simp at hdec; omega
    have hp := white_point_of_index (nextWhiteIndex w) 2 0 (by dsimp [nextWhiteIndex]; omega) (by
      dsimp [nextWhiteIndex]; rw [hi,Nat.mod_eq_of_lt (by omega)] <;> simp)
    simpa [turn,nextWhiteIndex] using hp
  · have hi : w.2.val+1=3*(2*w.1.val+1) := by simp at hdec; omega
    have hp := white_point_of_index (nextWhiteIndex w) 3 0 (by dsimp [nextWhiteIndex]; omega) (by
      dsimp [nextWhiteIndex]; rw [hi,Nat.mod_eq_of_lt (by omega)] <;> simp)
    simpa [turn,nextWhiteIndex] using hp
  · have hi : w.2.val+1=8*w.1.val+4 := by simp at hdec; omega
    have hp := white_point_of_index (nextWhiteIndex w) 0 0 (by dsimp [nextWhiteIndex]; omega) (by
      dsimp [nextWhiteIndex]; rw [hi,Nat.mod_self] <;> simp)
    simpa [turn,nextWhiteIndex] using hp

end PlanarHom.RadialPottsTileCoordinates
