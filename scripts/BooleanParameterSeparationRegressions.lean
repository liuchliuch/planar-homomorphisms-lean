import PlanarHom.BooleanParameterSeparation

open PlanarHom.BooleanParameterSeparation

-- Equal theta and unequal positive weights separate at every positive exponent.
example {t : ℕ} (ht : 0 < t) : beta 2 (1 / 2) t ≠ beta 2 (1 / 3) t := by
  intro h
  have heq := (beta_eq_iff_weight_eq (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 3) ht).mp h
  norm_num at heq

-- Different theta values are separated without assuming a finite collision bound.
example : ∀ᶠ t : ℕ in Filter.atTop, beta 2 (1 / 100) t < beta 3 (1 / 2) t :=
  eventually_beta_lt_of_theta_lt (by norm_num) (by norm_num) (by norm_num)

-- Actual repeated coordinate pairs give one class; another class is distinct.
example : ∃ t : ℕ, 0 < t ∧ Odd t ∧
    beta 2 (1 / 2) t = beta 2 (1 / 2) t ∧
    beta 2 (1 / 2) t ≠ beta 3 (1 / 2) t := by
  let θ : ℕ → ℝ := fun i => if i = 2 then 3 else 2
  let w : ℕ → ℝ := fun _ => 1 / 2
  obtain ⟨t, ht, ho, hs⟩ := exists_positive_odd_separating ({0, 1, 2} : Finset ℕ)
    θ w (by intros; norm_num [w])
  refine ⟨t, ht, ho, ?_, ?_⟩
  · have h01 := (hs 0 (by simp) 1 (by simp) (by norm_num [θ]) (by norm_num [θ])).mpr
      (by norm_num [θ, w])
    simpa [θ, w] using h01
  · have h02 := hs 0 (by simp) 2 (by simp) (by norm_num [θ]) (by norm_num [θ])
    simpa [θ, w] using h02

-- Empty families still yield a positive odd exponent, even above a large lower bound.
example : ∃ t : ℕ, 1000 ≤ t ∧ 0 < t ∧ Odd t ∧
    Separates (∅ : Finset ℕ) (fun _ => 1) (fun _ => 0) t :=
  exists_positive_odd_separating_above ∅ _ _ (by simp) 1000

-- Singleton class API is nonvacuous in positivity and imposes no false size bound.
example : ∃ t : ℕ, 0 < t ∧ Odd t ∧
    Separates ({0} : Finset ℕ) (fun _ => 2) (fun _ => 1 / 2) t :=
  exists_positive_odd_separating {0} _ _ (by intros; norm_num)

-- Equal diagonal classes of different weights deliberately do not become injective.
example (t : ℕ) : beta 1 (1 / 2) t = beta 1 (1 / 3) t := by simp

-- Zero exponent cannot provide separation for distinct unequal-diagonal pairs.
example : beta 2 (1 / 2) 0 = beta 3 (1 / 3) 0 := by simp [beta]

-- The finite set interface supplies genuine injectivity and positivity.
example : ∃ t : ℕ, 0 < t ∧ Odd t ∧
    (∀ p ∈ ({(2, 1 / 2), (2, 1 / 3), (3, 1 / 2), (1, 1 / 4)} : Finset (ℝ × ℝ)),
      0 ≤ beta p.1 p.2 t) ∧
    (∀ p ∈ ({(2, 1 / 2), (2, 1 / 3), (3, 1 / 2), (1, 1 / 4)} : Finset (ℝ × ℝ)),
      1 < p.1 → 0 < beta p.1 p.2 t) ∧
    Set.InjOn (fun p : ℝ × ℝ => beta p.1 p.2 t)
      {p | p ∈ ({(2, 1 / 2), (2, 1 / 3), (3, 1 / 2), (1, 1 / 4)} : Finset (ℝ × ℝ)) ∧
        1 < p.1} := by
  apply exists_positive_odd_injOn
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num

-- The representative theorem makes no hidden assumption about beta collisions.
example : ∃ t : ℕ, 0 < t ∧ Odd t ∧
    (∀ i ∈ ({0, 1} : Finset ℕ), 1 < (2 : ℝ) → 0 < beta 2 (if i = 0 then 1 / 2 else 1 / 3) t) ∧
    Set.InjOn (fun i : ℕ => beta 2 (if i = 0 then 1 / 2 else 1 / 3) t)
      {i | i ∈ ({0, 1} : Finset ℕ) ∧ 1 < (2 : ℝ)} := by
  apply exists_positive_odd_representatives {0, 1} (fun _ => 2)
    (fun i => if i = 0 then 1 / 2 else 1 / 3)
  · intro i _
    split_ifs <;> norm_num
  · intro i hi j hj h
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    all_goals first | rfl | norm_num at h
