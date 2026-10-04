import PlanarHom.PlanarNeighborhoods

/-! NEW endpoint-complete injectivity of an ordinary non-loop edge. -/
namespace PlanarHom.MultiGraph.PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

theorem edgePath_injective (d : PlaneDrawing G) (e : E) (hne : G.src e≠G.dst e) :
    Function.Injective (d.curve e) := by
  have zero_unique (t) (h : d.curve e t=d.curve e 0) : t=0 := by
    rw [d.curve_zero] at h
    rcases (d.curve_eq_point_iff e t (G.src e)).mp h with h|h
    · exact h.1
    · exact False.elim (hne h.2.symm)
  have one_unique (t) (h : d.curve e t=d.curve e 1) : t=1 := by
    rw [d.curve_one] at h
    rcases (d.curve_eq_point_iff e t (G.dst e)).mp h with h|h
    · exact False.elim (hne h.2)
    · exact h.1
  intro s t h
  by_cases hs0:s=0
  · subst s; exact (zero_unique t h.symm).symm
  by_cases hs1:s=1
  · subst s; exact (one_unique t h.symm).symm
  by_cases ht0:t=0
  · subst t; exact zero_unique s h
  by_cases ht1:t=1
  · subst t; exact one_unique s h
  exact (d.interior_injective e e s t (inside_of_ne_endpoints hs0 hs1)
    (inside_of_ne_endpoints ht0 ht1) h).2

end PlanarHom.MultiGraph.PlaneDrawing
