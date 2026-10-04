import PlanarHom.RadialPottsTileEdgeModel
import PlanarHom.RadialPottsTileCoordinateIndices

/-! NEW literal endpoints of every long radial occurrence, including ports. -/
namespace PlanarHom.RadialPottsTileGeometry
open IntegerStraightDrawing RadialPottsTile RadialPottsTileCoordinates

theorem long_start {k : ℕ} (e : Long k) :
    point ((graph k).src (.inl e))=(edgeSegment (.inl e)).start k := by
  have hh := white_point_of_index (longLeft e) e.2.1 (2*e.2.2.val)
    (by dsimp [longLeft]; have:=e.2.2.isLt; omega) rfl
  change point (.inl (longLeft e))=_
  rw [hh]
  simp [edgeSegment,Segment.start,RadialPottsTileCoordinates.turn,turn,longLeft]

theorem long_finish {k : ℕ} (e : Long k) :
    point ((graph k).dst (.inl e))=(edgeSegment (.inl e)).finish := by
  change point (longRight e)=_
  unfold longRight
  split_ifs with hr
  · have hh := white_point_of_index
      (⟨⟨e.1.val+1,hr⟩,⟨e.2.1.val*(2*(e.1.val+1)+1)+2*e.2.2.val+1,by
        have:=e.2.1.isLt; have:=e.2.2.isLt
        have hm:=Nat.mul_le_mul_right (2*(e.1.val+1)+1) (show e.2.1.val≤3 by omega)
        change _ < 8*(e.1.val+1)+4
        omega⟩⟩ : White k) e.2.1 (2*e.2.2.val+1)
      (by have:=e.2.2.isLt; dsimp; omega) (by dsimp; omega)
    rw [hh]
    simp only [edgeSegment,Segment.finish,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    change RadialPottsTileCoordinates.turn e.2.1 _=RadialPottsTileCoordinates.turn e.2.1 _
    congr 1
    ext <;> dsimp <;> ring
  · have hk : k=e.1.val+1 := by have:=e.1.isLt; omega
    simp only [point,edgeSegment,Segment.finish,hk,Nat.cast_add,Nat.cast_one]
    change RadialPottsTileCoordinates.turn e.2.1 _=RadialPottsTileCoordinates.turn e.2.1 _
    congr 1
    ext <;> dsimp <;> ring

end PlanarHom.RadialPottsTileGeometry
