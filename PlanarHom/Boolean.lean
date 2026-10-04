import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Boolean Ising tensors and their characters

This file formalizes the finite algebra in equations (1.1) and Section 2.6 of
Liu--Meng, *A Dichotomy for Planar Graph Homomorphisms with Nonnegative Weights*.
It makes no claim about an algorithm, planar gadgets, or counting complexity.
Characters are indexed by bit vectors, equivalently subsets of coordinates.
-/

noncomputable section

namespace PlanarHom.Boolean

open scoped BigOperators

/-- The two-state zero-field Ising interaction. -/
def W (ρ : ℝ) (x y : Bool) : ℝ := if x = y then 1 else ρ

@[simp] theorem W_diag (ρ : ℝ) (x : Bool) : W ρ x x = 1 := by simp [W]

theorem W_symm (ρ : ℝ) (x y : Bool) : W ρ x y = W ρ y x := by
  simp [W, eq_comm]

@[simp] theorem W_one (x y : Bool) : W 1 x y = 1 := by simp [W]

theorem W_pos {ρ : ℝ} (hρ : 0 < ρ) (x y : Bool) : 0 < W ρ x y := by
  by_cases h : x = y <;> simp [W, h, hρ]

theorem W_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (x y : Bool) : 0 ≤ W ρ x y := by
  by_cases h : x = y <;> simp [W, h, hρ]

theorem W_mul (ρ σ : ℝ) (x y : Bool) :
    W (ρ * σ) x y = W ρ x y * W σ x y := by
  by_cases h : x = y <;> simp [W, h]

theorem W_pow (ρ : ℝ) (n : ℕ) (x y : Bool) : W (ρ ^ n) x y = W ρ x y ^ n := by
  by_cases h : x = y <;> simp [W, h]

theorem W_xor (ρ : ℝ) (x y z : Bool) :
    W ρ (Bool.xor x z) (Bool.xor y z) = W ρ x y := by
  cases x <;> cases y <;> cases z <;> simp [W]

/-- Coordinates of a Boolean tensor with `d` factors. -/
abbrev Cube (d : ℕ) := Fin d → Bool

/-- Entry of the tensor product of the individual Ising interactions. -/
def tensor {d : ℕ} (ρ : Fin d → ℝ) (x y : Cube d) : ℝ := ∏ i, W (ρ i) (x i) (y i)

@[simp] theorem tensor_diag {d : ℕ} (ρ : Fin d → ℝ) (x : Cube d) :
    tensor ρ x x = 1 := by simp [tensor]

theorem tensor_symm {d : ℕ} (ρ : Fin d → ℝ) (x y : Cube d) :
    tensor ρ x y = tensor ρ y x := by
  simp only [tensor, W_symm]

@[simp] theorem tensor_empty (ρ : Fin 0 → ℝ) (x y : Cube 0) : tensor ρ x y = 1 := by
  simp [tensor]

@[simp] theorem tensor_one {d : ℕ} (x y : Cube d) : tensor (fun _ => 1) x y = 1 := by
  simp [tensor]

theorem tensor_pos {d : ℕ} {ρ : Fin d → ℝ} (hρ : ∀ i, 0 < ρ i) (x y : Cube d) :
    0 < tensor ρ x y := by
  exact Finset.prod_pos fun i _ => W_pos (hρ i) _ _

theorem tensor_nonneg {d : ℕ} {ρ : Fin d → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (x y : Cube d) :
    0 ≤ tensor ρ x y := by
  exact Finset.prod_nonneg fun i _ => W_nonneg (hρ i) _ _

/-- Parallel multiplication is coordinatewise multiplication of Ising parameters. -/
theorem tensor_mul {d : ℕ} (ρ σ : Fin d → ℝ) (x y : Cube d) :
    tensor (fun i => ρ i * σ i) x y = tensor ρ x y * tensor σ x y := by
  simp only [tensor, W_mul, Finset.prod_mul_distrib]

theorem tensor_pow {d : ℕ} (ρ : Fin d → ℝ) (n : ℕ) (x y : Cube d) :
    tensor (fun i => ρ i ^ n) x y = tensor ρ x y ^ n := by
  simp only [tensor, W_pow, Finset.prod_pow]

/-- Splitting the coordinates gives precisely a Kronecker product entry. -/
theorem tensor_split {a b : ℕ} (ρ : Fin (a + b) → ℝ) (x y : Cube (a + b)) :
    tensor ρ x y =
      tensor (fun i => ρ (Fin.castAdd b i)) (fun i => x (Fin.castAdd b i))
        (fun i => y (Fin.castAdd b i)) *
      tensor (fun i => ρ (Fin.natAdd a i)) (fun i => x (Fin.natAdd a i))
        (fun i => y (Fin.natAdd a i)) := by
  exact Fin.prod_univ_add _

theorem tensor_succ {d : ℕ} (ρ : Fin (d + 1) → ℝ) (x y : Cube (d + 1)) :
    tensor ρ x y = W (ρ 0) (x 0) (y 0) *
      tensor (fun i => ρ i.succ) (fun i => x i.succ) (fun i => y i.succ) := by
  exact Fin.prod_univ_succ _

/-- A unit bit vector, with only coordinate `r` set to true. -/
def unitBit {d : ℕ} (r : Fin d) : Cube d := fun i => decide (i = r)

/-- The parameter at a coordinate can be read from a single-flip entry. -/
theorem tensor_unitBit {d : ℕ} (ρ : Fin d → ℝ) (r : Fin d) :
    tensor ρ (fun _ => false) (unitBit r) = ρ r := by
  have h (i : Fin d) : W (ρ i) false (unitBit r i) = if i = r then ρ i else 1 := by
    by_cases hi : i = r <;> simp [W, unitBit, hi]
  simp only [tensor, h]
  simp

/-- The all-one tensor degeneracy occurs exactly when every parameter is one. -/
theorem tensor_eq_one_iff {d : ℕ} (ρ : Fin d → ℝ) :
    (∀ x y : Cube d, tensor ρ x y = 1) ↔ ∀ i, ρ i = 1 := by
  constructor
  · intro h i
    simpa only [tensor_unitBit] using h (fun _ => false) (unitBit i)
  · intro h x y
    simp [tensor, h]

/-- Reading single-flip entries recovers all tensor parameters. -/
theorem tensor_injective {d : ℕ} {ρ σ : Fin d → ℝ}
    (h : ∀ x y : Cube d, tensor ρ x y = tensor σ x y) : ρ = σ := by
  funext i
  simpa only [tensor_unitBit] using h (fun _ => false) (unitBit i)

theorem tensor_pos_iff {d : ℕ} (ρ : Fin d → ℝ) :
    (∀ x y : Cube d, 0 < tensor ρ x y) ↔ ∀ i, 0 < ρ i := by
  constructor
  · intro h i
    simpa only [tensor_unitBit] using h (fun _ => false) (unitBit i)
  · exact fun h x y => tensor_pos h x y

theorem tensor_nonneg_iff {d : ℕ} (ρ : Fin d → ℝ) :
    (∀ x y : Cube d, 0 ≤ tensor ρ x y) ↔ ∀ i, 0 ≤ ρ i := by
  constructor
  · intro h i
    simpa only [tensor_unitBit] using h (fun _ => false) (unitBit i)
  · exact fun h x y => tensor_nonneg h x y

/-- The one-bit character, with its character index listed first. -/
def bitCharacter (s x : Bool) : ℝ := if s && x then -1 else 1

@[simp] theorem bitCharacter_false (x : Bool) : bitCharacter false x = 1 := by
  simp [bitCharacter]

theorem bitCharacter_symm (s x : Bool) : bitCharacter s x = bitCharacter x s := by
  cases s <;> cases x <;> rfl

theorem bitCharacter_mul (s t x : Bool) :
    bitCharacter s x * bitCharacter t x = bitCharacter (Bool.xor s t) x := by
  cases s <;> cases t <;> cases x <;> norm_num [bitCharacter]

theorem bitCharacter_orthogonality (s t : Bool) :
    (∑ x : Bool, bitCharacter s x * bitCharacter t x) = if s = t then 2 else 0 := by
  cases s <;> cases t <;> norm_num [Fintype.sum_bool, bitCharacter]

/-- The one-bit Fourier eigenvector identity. -/
theorem W_character (ρ : ℝ) (s x : Bool) :
    (∑ y : Bool, W ρ x y * bitCharacter s y) =
      (1 + (if s then -1 else 1) * ρ) * bitCharacter s x := by
  cases s <;> cases x <;> simp [W, bitCharacter] <;> ring

/-- Addition of character indices, equivalently symmetric difference of subsets. -/
def xor {d : ℕ} (s t : Cube d) : Cube d := fun i => Bool.xor (s i) (t i)

theorem tensor_xor {d : ℕ} (ρ : Fin d → ℝ) (x y z : Cube d) :
    tensor ρ (xor x z) (xor y z) = tensor ρ x y := by
  simp only [tensor, xor, W_xor]

/-- The real-valued Walsh character indexed by a subset of coordinates. -/
def character {d : ℕ} (s x : Cube d) : ℝ := ∏ i, bitCharacter (s i) (x i)

@[simp] theorem character_zero {d : ℕ} (x : Cube d) : character (fun _ => false) x = 1 := by
  simp [character]

theorem character_symm {d : ℕ} (s x : Cube d) : character s x = character x s := by
  simp only [character, bitCharacter_symm]

/-- The character product law `χ_S χ_T = χ_(S △ T)`. -/
theorem character_mul {d : ℕ} (s t x : Cube d) :
    character s x * character t x = character (xor s t) x := by
  simp only [character, ← Finset.prod_mul_distrib, bitCharacter_mul, xor]

@[simp] theorem character_mul_self {d : ℕ} (s x : Cube d) :
    character s x * character s x = 1 := by
  rw [character_mul]
  simp [xor, character, bitCharacter]

theorem character_xor {d : ℕ} (s x y : Cube d) :
    character s (xor x y) = character s x * character s y := by
  rw [character_symm s (xor x y), ← character_mul,
    character_symm x s, character_symm y s]

theorem character_unitBit {d : ℕ} (s : Cube d) (r : Fin d) :
    character s (unitBit r) = if s r then -1 else 1 := by
  have h (i : Fin d) : bitCharacter (s i) (unitBit r i) =
      if i = r then (if s i then -1 else 1) else 1 := by
    by_cases hi : i = r
    · subst i
      cases s r <;> simp [bitCharacter, unitBit]
    · simp [bitCharacter, unitBit, hi]
  simp only [character, h]
  simp

/-- Flipping coordinate `r` multiplies a character by its `r`-th sign. -/
theorem character_flip {d : ℕ} (s x : Cube d) (r : Fin d) :
    character s (xor x (unitBit r)) = (if s r then -1 else 1) * character s x := by
  rw [character_xor, character_unitBit, mul_comm]

/-- Unnormalized Walsh orthogonality, including the empty cube. -/
theorem character_orthogonality {d : ℕ} (s t : Cube d) :
    (∑ x : Cube d, character s x * character t x) =
      if s = t then (2 : ℝ) ^ d else 0 := by
  classical
  simp only [character, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin d) (x : Bool) =>
    bitCharacter (s i) x * bitCharacter (t i) x)]
  simp only [bitCharacter_orthogonality]
  by_cases h : s = t
  · subst t
    simp
  · simp only [h, ↓reduceIte]
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ t i := by
      by_contra hn
      apply h
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Product eigenvalue of the Ising tensor at a Walsh character. -/
def eigenvalue {d : ℕ} (ρ : Fin d → ℝ) (s : Cube d) : ℝ :=
  ∏ i, (1 + (if s i then -1 else 1) * ρ i)

/-- The tensor Ising kernel is diagonal on the Walsh characters. -/
theorem tensor_character {d : ℕ} (ρ : Fin d → ℝ) (s x : Cube d) :
    (∑ y : Cube d, tensor ρ x y * character s y) = eigenvalue ρ s * character s x := by
  unfold tensor character eigenvalue
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin d) (y : Bool) =>
    W (ρ i) (x i) y * bitCharacter (s i) y)]
  simp only [W_character]

/-- A tensor row sums to the product of `1 + ρᵢ`. -/
theorem tensor_row_sum {d : ℕ} (ρ : Fin d → ℝ) (x : Cube d) :
    (∑ y : Cube d, tensor ρ x y) = ∏ i, (1 + ρ i) := by
  simpa [eigenvalue] using tensor_character ρ (fun _ => false) x

/-- Both Walsh coordinate changes, without the normalization factor. -/
theorem tensor_walsh_diagonal {d : ℕ} (ρ : Fin d → ℝ) (s t : Cube d) :
    (∑ x : Cube d, ∑ y : Cube d,
      character s x * tensor ρ x y * character t y) =
      if s = t then (2 : ℝ) ^ d * eigenvalue ρ s else 0 := by
  classical
  calc
    _ = ∑ x : Cube d, character s x *
        (∑ y : Cube d, tensor ρ x y * character t y) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [Finset.mul_sum, mul_assoc]
    _ = eigenvalue ρ t * (∑ x : Cube d, character s x * character t x) := by
      simp only [tensor_character, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [character_orthogonality]
      by_cases h : s = t
      · subst t
        simp [mul_comm]
      · simp [h]

/-- The unnormalized Fourier transform. Normalization is supplied by inversion. -/
def walshTransform {d : ℕ} (f : Cube d → ℝ) (s : Cube d) : ℝ :=
  ∑ x : Cube d, character s x * f x

/-- Applying the unnormalized Walsh transform twice multiplies by the cube size. -/
theorem walshTransform_involution {d : ℕ} (f : Cube d → ℝ) (x : Cube d) :
    walshTransform (walshTransform f) x = (2 : ℝ) ^ d * f x := by
  classical
  unfold walshTransform
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  calc
    _ = ∑ y : Cube d, (∑ s : Cube d, character x s * character y s) * f y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [character_symm s y]
    _ = ∑ y : Cube d, (if x = y then (2 : ℝ) ^ d else 0) * f y := by
      simp_rw [character_orthogonality]
    _ = _ := by simp

/-- Entrywise multiplication becomes convolution in Walsh coordinates.
The factor `2^d` appears because `walshTransform` is unnormalized. -/
theorem walshTransform_mul {d : ℕ} (f g : Cube d → ℝ) (s : Cube d) :
    (∑ t : Cube d, walshTransform f t * walshTransform g (xor s t)) =
      (2 : ℝ) ^ d * walshTransform (fun x => f x * g x) s := by
  classical
  have hinv (x : Cube d) :
      (∑ t : Cube d, character t x * walshTransform f t) = (2 : ℝ) ^ d * f x := by
    calc
      _ = walshTransform (walshTransform f) x := by
        unfold walshTransform
        apply Finset.sum_congr rfl
        intro t _
        rw [character_symm t x]
      _ = _ := walshTransform_involution f x
  calc
    _ = ∑ t : Cube d, ∑ x : Cube d,
        walshTransform f t * (character (xor s t) x * g x) := by
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.mul_sum _ _ _
    _ = ∑ x : Cube d, ∑ t : Cube d,
        walshTransform f t * (character (xor s t) x * g x) := Finset.sum_comm
    _ = ∑ x : Cube d, character s x *
        ((∑ t : Cube d, character t x * walshTransform f t) * g x) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [Finset.sum_mul, Finset.mul_sum, ← character_mul]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ∑ x : Cube d, character s x * (((2 : ℝ) ^ d * f x) * g x) := by
      simp only [hinv]
    _ = _ := by
      unfold walshTransform
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- One factor of the Boolean noise kernel. -/
def bitNoise (z : ℝ) (x y : Bool) : ℝ := if x = y then (1 + z) / 2 else (1 - z) / 2

theorem bitNoise_character (z : ℝ) (s x : Bool) :
    (∑ y : Bool, bitNoise z x y * bitCharacter s y) =
      (if s then z else 1) * bitCharacter s x := by
  cases s <;> cases x <;> simp [bitNoise, bitCharacter] <;> ring

/-- The degree of a Walsh character, or cardinality of its indexing subset. -/
def degree {d : ℕ} (s : Cube d) : ℕ := ∑ i, if s i then 1 else 0

/-- The product formula for the Boolean noise kernel in Section 2.6. -/
def noise {d : ℕ} (z : ℝ) (x y : Cube d) : ℝ := ∏ i, bitNoise z (x i) (y i)

/-- The Boolean noise operator has eigenvalue `z ^ degree s` on character `s`. -/
theorem noise_character {d : ℕ} (z : ℝ) (s x : Cube d) :
    (∑ y : Cube d, noise z x y * character s y) = z ^ degree s * character s x := by
  have hpow (i : Fin d) : (if s i then z else 1) = z ^ (if s i then 1 else 0 : ℕ) := by
    cases s i <;> simp
  have hprod : (∏ i, if s i then z else 1) = z ^ degree s := by
    simp only [hpow, degree, Finset.prod_pow_eq_pow_sum]
  calc
    _ = ∏ i, ∑ y : Bool, bitNoise z (x i) y * bitCharacter (s i) y := by
      simp only [noise, character, ← Finset.prod_mul_distrib, Fintype.prod_sum]
    _ = (∏ i, if s i then z else 1) * character s x := by
      simp only [bitNoise_character, Finset.prod_mul_distrib, character]
    _ = _ := by rw [hprod]

end PlanarHom.Boolean
