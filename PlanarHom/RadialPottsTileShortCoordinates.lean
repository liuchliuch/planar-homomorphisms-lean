import PlanarHom.RadialPottsTileEdgeModel
import PlanarHom.RadialPottsTileSwitchCoordinates

/-! NEW occurrence endpoints for all original short edges, including the
simultaneously switched red edges. -/
namespace PlanarHom.RadialPottsTileGeometry
open IntegerStraightDrawing RadialPottsTile RadialPottsTileCoordinates

theorem regular_short_src {k : ℕ} (e : HalfShort k × Bool)
    (hi : (shortIndex e).val≠0) :
    (graph k).src (.inr e)=.inl (shortWhite e) := by
  rcases e with ⟨h,b⟩
  cases b
  · have hz : ¬ ((evenWhite h).2.val=0 ∧ (evenWhite h).1.val+1<k) := by
      simp only [evenWhite]; simp only [shortIndex,Bool.false_eq_true,if_false,add_zero] at hi
      omega
    have ho : ¬ ((evenWhite h).2.val=1 ∧ 0<(evenWhite h).1.val) := by dsimp [evenWhite]; omega
    simp only [graph,Bool.false_eq_true,if_false,Sum.elim_inr,switch,dif_neg hz,dif_neg ho]
    rfl
  · rfl

theorem regular_short_dst {k : ℕ} (e : HalfShort k × Bool)
    (hi : (shortIndex e).val≠0) :
    (graph k).dst (.inr e)=.inl (nextWhiteIndex (shortWhite e)) := by
  rcases e with ⟨h,b⟩
  cases b
  · have hz : ¬ ((oddWhite h).2.val=0 ∧ (oddWhite h).1.val+1<k) := by dsimp [oddWhite]; omega
    have ho : ¬ ((oddWhite h).2.val=1 ∧ 0<(oddWhite h).1.val) := by
      simp only [shortIndex,Bool.false_eq_true,if_false,add_zero] at hi
      dsimp [oddWhite]; omega
    simp only [graph,Bool.false_eq_true,if_false,Sum.elim_inr,switch,dif_neg hz,dif_neg ho]
    apply congrArg Sum.inl
    apply white_ext (oddWhite h) (nextWhiteIndex (shortWhite (h,false))) rfl
    dsimp [oddWhite,nextWhiteIndex,shortWhite,shortIndex]
    have hh : 2*h.2.val+1<8*h.1.val+4 := by have:=h.2.isLt; omega
    rw [Nat.mod_eq_of_lt hh]
  · change (Sum.inl (nextWhite h) : Vertex k)=.inl (nextWhiteIndex (shortWhite (h,true)))
    apply congrArg Sum.inl
    apply white_ext (nextWhite h) (nextWhiteIndex (shortWhite (h,true))) rfl
    dsimp [nextWhite,nextWhiteIndex,shortWhite,shortIndex]

theorem short_zero_shape {k : ℕ} (e : HalfShort k × Bool)
    (hi : (shortIndex e).val=0) : e=(⟨e.1.1,0⟩,false) := by
  rcases e with ⟨⟨r,a⟩,b⟩
  cases b
  · have ha:a=0 := Fin.ext (by simp [shortIndex] at hi; omega)
    subst a
    rfl
  · simp [shortIndex] at hi

theorem short_start {k : ℕ} (e : HalfShort k × Bool) :
    point ((graph k).src (.inr e))=(edgeSegment (.inr e)).start k := by
  by_cases hi : (shortIndex e).val=0
  · have he:=short_zero_shape e hi
    rw [he]
    change point (.inl (switch (zeroWhite e.1.1)))=_
    rw [point_switch_zeroWhite]
    simp [edgeSegment,shortIndex,Segment.start]
    norm_cast
  · rw [regular_short_src e hi]
    have hh := white_point_of_index (shortWhite e) (whiteSide (shortWhite e))
      ((shortIndex e).val%(2*e.1.1.val+1))
      (Nat.mod_lt _ (by omega))
      (white_index_decomposition (shortWhite e))
    rw [hh]
    simp only [edgeSegment,hi,if_false]
    split_ifs with ht
    · rfl
    · have hm := Nat.mod_lt (shortIndex e).val (by omega : 0<2*e.1.1.val+1)
      have hm' : (shortIndex e).val%(2*e.1.1.val+1)=2*e.1.1.val := by omega
      simp only [Segment.start,hm',shortWhite,Nat.cast_mul,Nat.cast_ofNat]
      change RadialPottsTileCoordinates.turn _ _=RadialPottsTileCoordinates.turn _ _
      congr 1
      ext <;> dsimp <;> ring

theorem short_finish {k : ℕ} (e : HalfShort k × Bool) :
    point ((graph k).dst (.inr e))=(edgeSegment (.inr e)).finish := by
  by_cases hi : (shortIndex e).val=0
  · have he:=short_zero_shape e hi
    rw [he]
    change point (.inl (switch (oneWhite e.1.1)))=_
    rw [point_switch_oneWhite]
    simp [edgeSegment,shortIndex,Segment.finish]
  · rw [regular_short_dst e hi]
    simp only [edgeSegment,hi,if_false]
    split_ifs with ht
    · exact nextWhite_point_side (shortWhite e) ht
    · have hm := Nat.mod_lt (shortIndex e).val (by omega : 0<2*e.1.1.val+1)
      have hm' : (shortIndex e).val%(2*e.1.1.val+1)=2*e.1.1.val := by omega
      exact nextWhite_point_corner (shortWhite e) hm'

end PlanarHom.RadialPottsTileGeometry
