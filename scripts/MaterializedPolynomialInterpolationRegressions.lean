import PlanarHom.MaterializedPolynomialInterpolationMachines

open PlanarHom
open PlanarHom.MaterializedPolynomialInterpolationMachines

-- The compiled endpoint has the original field output codec and no growth promise.
example {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (x₀ : K) :
    Complexity.FP (inputEncoding basis) (Complexity.numberFieldEncoding basis) (recover x₀) :=
  fp_recover basis x₀

-- Signed nodes and values, including node zero; this is x² - 2x - 3 evaluated at 4.
example : recover (4 : ℚ) [(-1, 0), (0, -3), (2, -3)] = 5 := by
  norm_num [recover, rowTerm, differenceProduct, otherNodes]

-- The evaluation point is itself the zero node; no numerator inversion is used.
example : recover (0 : ℚ) [(-1, 0), (0, -3), (2, -3)] = -3 := by
  norm_num [recover, rowTerm, differenceProduct, otherNodes]

-- Nonzero evaluation at a node is also exact.
example : recover (2 : ℚ) [(-1, 0), (0, -3), (2, -3)] = -3 := by
  norm_num [recover, rowTerm, differenceProduct, otherNodes]

-- Signed fractional samples retain exact rational arithmetic.
example : recover (3 / 2 : ℚ) [(-1, 4), (0, -3), (2, 7)] = 3 / 2 := by
  norm_num [recover, rowTerm, differenceProduct, otherNodes]

example (x₀ : ℚ) : recover x₀ [] = 0 := recover_nil x₀
example (x₀ : ℚ) : recover x₀ [(0, -7)] = -7 := recover_singleton x₀ 0 (-7)

-- Invalid repeated nodes still have a total, explicitly specified behavior.
example (x₀ : ℚ) : recover x₀ [(0, 2), (0, 3)] = 5 := by
  norm_num [recover, rowTerm, differenceProduct, otherNodes]

-- Arbitrary signed samples and arbitrary evaluation points are covered semantically.
example {n : ℕ} (x₀ : ℚ) (nodes values : Fin n → ℚ)
    (hnodes : Function.Injective nodes) (P : Polynomial ℚ) (hdegree : P.degree < n)
    (hvalues : ∀ i, values i = P.eval (nodes i)) :
    recover x₀ (List.ofFn (fun i => (nodes i, values i))) = P.eval x₀ :=
  recover_ofFn_eq_eval x₀ nodes values hnodes P hdegree hvalues

-- The degree convention permits the empty table for the zero polynomial.
example (x₀ : ℚ) : recover x₀ (([] : List ℚ).map (fun x => (x, (0 : Polynomial ℚ).eval x))) =
    (0 : Polynomial ℚ).eval x₀ := by
  apply recover_samples x₀ [] (by simp) 0
  simp

example (table : List (ℚ × ℚ)) (hnodes : (table.map Prod.fst).Nodup)
    (y : ℚ) (hrow : (0, y) ∈ table) : recover 0 table = y :=
  recover_at_mem table hnodes 0 y hrow
