import Mathlib.Order.MinMax

/-! NEW strict separation/nesting predicates on arbitrary linearly ordered port
keys, with elementary endpoint-pattern introduction rules. -/
namespace PlanarHom

def PortNoncrossing {A : Type*} [LinearOrder A] (x y u v : A) : Prop :=
  max x y < min u v ∨ max u v < min x y ∨
    (min x y < min u v ∧ max u v < max x y) ∨
    (min u v < min x y ∧ max x y < max u v)

 theorem PortNoncrossing.symm {A : Type*} [LinearOrder A] {x y u v : A}
    (h : PortNoncrossing x y u v) : PortNoncrossing u v x y := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

 theorem PortNoncrossing.swap_left {A : Type*} [LinearOrder A] {x y u v : A}
    (h : PortNoncrossing x y u v) : PortNoncrossing y x u v := by
  simpa only [PortNoncrossing,min_comm y x,max_comm y x] using h

 theorem PortNoncrossing.swap_right {A : Type*} [LinearOrder A] {x y u v : A}
    (h : PortNoncrossing x y u v) : PortNoncrossing x y v u := by
  simpa only [PortNoncrossing,min_comm v u,max_comm v u] using h

 theorem portNoncrossing_separated {A : Type*} [LinearOrder A] {x y u v : A}
    (hxu : x < u) (hxv : x < v) (hyu : y < u) (hyv : y < v) : PortNoncrossing x y u v :=
  Or.inl (lt_min (max_lt hxu hyu) (max_lt hxv hyv))

 theorem portNoncrossing_inside {A : Type*} [LinearOrder A] {x y u v : A}
    (hux : u < x) (huy : u < y) (hxv : x < v) (hyv : y < v) : PortNoncrossing x y u v := by
  have huv : u < v := hux.trans hxv
  right; right; right
  rw [min_eq_left huv.le,max_eq_right huv.le]
  exact ⟨lt_min hux huy,max_lt hxv hyv⟩

end PlanarHom
