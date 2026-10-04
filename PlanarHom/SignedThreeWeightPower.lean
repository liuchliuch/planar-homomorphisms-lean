import PlanarHom.SignedThreeStateAlgebra

/-! A single global odd power removes every signed cancellation among three
positive weights. This is the finite-dimensional signed-gadget step, not a
complexity assertion. -/
namespace PlanarHom.SignedThreeState

/-- Signed sum with exactly three independently chosen signs. -/
def signedTriple (x y z : ℝ) (a b c : Bool) : ℝ :=
  (if a then -x else x)+(if b then -y else y)+(if c then -z else z)

theorem cube_add_strict (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    x^3+y^3<(x+y)^3 := by
  have h : 0<3*x*y*(x+y) := mul_pos (mul_pos (mul_pos (by norm_num) hx) hy) (add_pos hx hy)
  nlinarith

theorem signedTriple_ne_zero_of_dominates (x y z : ℝ)
    (hx : 0<x) (hy : 0<y) (hz : 0<z)
    (h : x+y<z ∨ x+z<y ∨ y+z<x) (a b c : Bool) :
    signedTriple x y z a b c≠0 := by
  cases a <;> cases b <;> cases c <;> rcases h with h|h|h <;>
    simp only [signedTriple,Bool.false_eq_true,↓reduceIte] <;> linarith

/-- If any signs cancel at exponent one, every sign choice is nonzero at
exponent three. The same power works simultaneously for every row pair. -/
theorem signedTriple_cube_nonzero_of_balance (x y z : ℝ)
    (hx : 0<x) (hy : 0<y) (hz : 0<z)
    (h : ∃a b c,signedTriple x y z a b c=0) :
    ∀a b c,signedTriple (x^3) (y^3) (z^3) a b c≠0 := by
  have hd : x+y=z ∨ x+z=y ∨ y+z=x := by
    obtain ⟨a,b,c,h⟩ := h
    cases a <;> cases b <;> cases c <;>
      simp only [signedTriple,Bool.false_eq_true,↓reduceIte] at h
    all_goals first | (exfalso; linarith) | (exact Or.inl (by linarith)) |
      (exact Or.inr (Or.inl (by linarith))) | (exact Or.inr (Or.inr (by linarith)))
  have hd' : x^3+y^3<z^3 ∨ x^3+z^3<y^3 ∨ y^3+z^3<x^3 := by
    rcases hd with h|h|h
    · exact Or.inl (h ▸ cube_add_strict x y hx hy)
    · exact Or.inr (Or.inl (h ▸ cube_add_strict x z hx hz))
    · exact Or.inr (Or.inr (h ▸ cube_add_strict y z hy hz))
  exact signedTriple_ne_zero_of_dominates (x^3) (y^3) (z^3)
    (pow_pos hx _) (pow_pos hy _) (pow_pos hz _) hd'

/-- One of two fixed odd exponents removes all three-term sign cancellations.
Selection depends only on the fixed source weights, never on the input graph. -/
theorem exists_global_odd_power (x y z : ℝ)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) :
    ∃k:ℕ,(k=1 ∨ k=3) ∧ ∀a b c,signedTriple (x^k) (y^k) (z^k) a b c≠0 := by
  classical
  by_cases h : ∃a b c,signedTriple x y z a b c=0
  · exact ⟨3,Or.inr rfl,signedTriple_cube_nonzero_of_balance x y z hx hy hz h⟩
  · refine ⟨1,Or.inl rfl,?_⟩
    intro a b c he
    exact h ⟨a,b,c,by simpa only [pow_one] using he⟩

end PlanarHom.SignedThreeState
