import PlanarHom.RadialPottsTileCoordinates

/-! NEW exact closed box bounds and strict white-vertex bounds. -/
namespace PlanarHom.RadialPottsTileCoordinates
open IntegerStraightDrawing RadialPottsTile

theorem white_box {k : ℕ} (w : White k) :
    -(k:ℤ)-1<(point (.inl w)).1 ∧ (point (.inl w)).1<(k:ℤ)+1 ∧
    -(k:ℤ)-1<(point (.inl w)).2 ∧ (point (.inl w)).2<(k:ℤ)+1 := by
  have hb:=whiteOffset_bounds w
  have hr:=w.1.isLt
  simp only [point]
  generalize whiteSide w=s
  fin_cases s <;> norm_num [turn] <;> omega

theorem point_box {k : ℕ} (v : Vertex k) :
    -(k:ℤ)-1≤(point v).1 ∧ (point v).1≤(k:ℤ)+1 ∧
    -(k:ℤ)-1≤(point v).2 ∧ (point v).2≤(k:ℤ)+1 := by
  cases v with
  | inl w => have hh:=white_box w; omega
  | inr p =>
    have hh:=portOffset_bounds p.2
    rcases p with ⟨s,a⟩
    fin_cases s <;> norm_num [point,turn] <;> omega

end PlanarHom.RadialPottsTileCoordinates
