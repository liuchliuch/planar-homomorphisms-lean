import PlanarHom.RadialPottsTileSegmentModel

/-! NEW exact vertex avoidance: every model edge has a unit integer coordinate
span, so its open segment contains no integer point at all. -/
namespace PlanarHom.RadialPottsTileGeometry
open IntegerStraightDrawing

theorem Segment.unitCoordinate (k : ℤ) (e : Segment) :
    |e.finish.1-(e.start k).1|=1 ∨ |e.finish.2-(e.start k).2|=1 := by
  cases e with
  | long r s a => fin_cases s <;> simp [Segment.start,Segment.finish,turn] <;> omega
  | side r s t => fin_cases s <;> simp [Segment.start,Segment.finish,turn] <;> omega
  | corner r s => fin_cases s <;> simp [Segment.start,Segment.finish,turn] <;> omega
  | special r => simp [Segment.start,Segment.finish]

theorem Segment.avoids (k : ℤ) (e : Segment) (p : Point) :
    Avoids (e.start k) e.finish p := by
  have avoid_unit (a b c : ℤ) (h : |b-a|=1) : coordinateAvoid a b c := by
    unfold coordinateAvoid
    by_cases hh : 0≤b-a
    · rw [abs_of_nonneg hh] at h
      omega
    · rw [abs_of_neg (by omega : b-a<0)] at h
      omega
  rcases e.unitCoordinate k with h|h
  · exact Or.inr (Or.inl (avoid_unit _ _ _ h))
  · exact Or.inr (Or.inr (avoid_unit _ _ _ h))

theorem Segment.nondegenerate (k : ℤ) (e : Segment) : e.start k≠e.finish := by
  intro he
  have hh := e.unitCoordinate k
  rw [he] at hh
  simp at hh

end PlanarHom.RadialPottsTileGeometry
