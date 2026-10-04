import PlanarHom.BooleanSpectralCounts

open scoped BigOperators
open PlanarHom.BooleanSpectralCounts

-- Repeated coordinates stay distinct, and negative branch values are allowed.
example : count (fun _ : Fin 2 => (0 : Fin 1))
    (fun e : Fin 2 => fun i : Fin 2 => decide (e = i)) 0 = 2 := by decide

example :
    (∏ e : Fin 2, ∏ i : Fin 2,
      if decide (e = i) then (-3 : ℤ) else 2) =
      (2 : ℤ) ^ (total (fun _ : Fin 2 => (0 : Fin 1)) 2 0 -
        count (fun _ : Fin 2 => (0 : Fin 1)) (fun e i => decide (e = i)) 0) *
      (-3 : ℤ) ^ count (fun _ : Fin 2 => (0 : Fin 1))
        (fun e i => decide (e = i)) 0 := by
  simpa using product_eq_grouped (fun _ : Fin 2 => (0 : Fin 1))
    (fun e : Fin 2 => fun i => decide (e = i)) (fun _ => (2 : ℤ)) (fun _ => -3)

-- A zero branch with exponent zero contributes one; cancellation is never used.
example :
    (∏ e : Fin 1, ∏ i : Fin 2,
      if (fun _ _ => false) e i then (0 : ℤ) else -2) =
      (-2 : ℤ) ^ (total (fun _ : Fin 2 => (0 : Fin 1)) 1 0 -
        count (fun _ : Fin 2 => (0 : Fin 1)) (fun (_ : Fin 1) _ => false) 0) *
      (0 : ℤ) ^ count (fun _ : Fin 2 => (0 : Fin 1))
        (fun (_ : Fin 1) _ => false) 0 := by
  simpa using product_eq_grouped (fun _ : Fin 2 => (0 : Fin 1))
    (fun (_ : Fin 1) _ => false) (fun _ => (-2 : ℤ)) (fun _ => 0)

-- Empty edge and coordinate types, and unused classes, remain legal inputs.
example (cls : Fin 2 → Fin 3) (choice : Fin 0 → Fin 2 → Bool) (g : Fin 3) :
    count cls choice g = 0 := count_no_edges cls choice g

example (choice : Fin 3 → Fin 0 → Bool) (g : Fin 2) :
    count Fin.elim0 choice g = 0 := by
  apply count_eq_zero_of_multiplicity_eq_zero
  simp [multiplicity]

example : count (fun _ : Fin 2 => (0 : Fin 2))
    (fun (_ : Fin 3) _ => true) 1 = 0 := by decide

example {R : Type*} [CommMonoid R] (cls : Fin 0 → Fin 0)
    (choice : Fin 0 → Fin 0 → Bool) (plus minus : Fin 0 → R) :
    (∏ e, ∏ i, if choice e i then minus (cls i) else plus (cls i)) =
      ∏ g, plus g ^ (total cls 0 g - count cls choice g) * minus g ^ count cls choice g :=
  product_eq_grouped cls choice plus minus

-- Retention discards nonretained zero factors and depends on only one count.
example :
    (∏ e : Fin 1, ∏ i : Fin 2, if i = 0 then
      (if (fun _ _ => false) e i then (-3 : ℤ) else 2) else 1) =
      (2 : ℤ) ^ (total (id : Fin 2 → Fin 2) 1 0 -
        count (id : Fin 2 → Fin 2) (fun (_ : Fin 1) _ => false) 0) *
      (-3 : ℤ) ^ count (id : Fin 2 → Fin 2) (fun (_ : Fin 1) _ => false) 0 := by
  simpa using retained_product_eq (id : Fin 2 → Fin 2)
    (fun (_ : Fin 1) _ => false) (fun i => if i = 0 then (2 : ℤ) else 0)
    (fun i => if i = 0 then (-3 : ℤ) else 0) 0
