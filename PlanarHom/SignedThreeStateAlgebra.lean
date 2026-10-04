import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Exact signed algebra for Theorem 2.3. These lemmas do not assert a
complexity classification. In particular signs are never discarded from the
original matrix when classifying its easy cases. -/
noncomputable section
namespace PlanarHom.SignedThreeState

variable {K : Type*} [CommRing K]

def booleanMatrix (a b c : K) : Matrix (Fin 2) (Fin 2) K := !![a,b;b,c]

def blockMatrix (a b c t : K) : Matrix (Fin 3) (Fin 3) K :=
  !![a,b,0;b,c,0;0,0,t]

def starMatrix (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0,0,a;0,0,b;a,b,0]

/-- The exact exceptional list includes the signed Boolean fourth case. -/
def BooleanEasy (a b c : K) : Prop :=
  a*c=b^2 ∨ b=0 ∨ a=c ∨ (a*c=-(b^2) ∧ a=-c)

def schurSquare {n : Type*} (M : Matrix n n K) : Matrix n n K := fun i j => (M i j)^2

/-- A rank-two matrix whose third column is the indicated linear combination. -/
def rankTwoChart (x y z α β : K) : Matrix (Fin 3) (Fin 3) K :=
  !![x,y,α*x+β*y;
     y,z,α*y+β*z;
     α*x+β*y,α*y+β*z,α^2*x+2*α*β*y+β^2*z]

theorem det_booleanMatrix (a b c : K) :
    (booleanMatrix a b c).det = a*c-b^2 := by
  simp [booleanMatrix,Matrix.det_fin_two,pow_two]

theorem det_starMatrix (a b : K) : (starMatrix a b).det = 0 := by
  simp [starMatrix,Matrix.det_fin_three]

theorem det_blockMatrix (a b c t : K) :
    (blockMatrix a b c t).det = (a*c-b^2)*t := by
  simp [blockMatrix,Matrix.det_fin_three]
  ring

theorem det_rankTwoChart (x y z α β : K) :
    (rankTwoChart x y z α β).det = 0 := by
  simp [rankTwoChart,Matrix.det_fin_three]
  ring

/-- CM23 Lemma 41's decisive identity, checked as a polynomial identity over
any commutative ring. The square is entrywise, not matrix multiplication. -/
theorem det_schurSquare_rankTwoChart (x y z α β : K) :
    (schurSquare (rankTwoChart x y z α β)).det =
      2*α^2*β^2*(x*z-y^2)^3 := by
  simp [schurSquare,rankTwoChart,Matrix.det_fin_three]
  ring

section Real

theorem schurSquare_nonnegative {n : Type*} (M : Matrix n n ℝ) :
    ∀i j, 0 ≤ schurSquare M i j := fun i j => sq_nonneg (M i j)

theorem schurSquare_eq_zero_iff {n : Type*} (M : Matrix n n ℝ) (i j : n) :
    schurSquare M i j=0 ↔ M i j=0 := by
  exact sq_eq_zero_iff

theorem schurSquare_rankTwoChart_det_ne_zero (x y z α β : ℝ)
    (ha : α≠0) (hb : β≠0) (hdet : x*z≠y^2) :
    (schurSquare (rankTwoChart x y z α β)).det≠0 := by
  rw [det_schurSquare_rankTwoChart]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha))
    (pow_ne_zero _ hb)) (pow_ne_zero _ (sub_ne_zero.mpr hdet))

/-- Over the reals the exceptional branch is exactly a signed Hadamard block
up to one scalar. Zero scalar is permitted. -/
theorem boolean_exceptional_iff (a b c : ℝ) :
    (a*c=-(b^2) ∧ a=-c) ↔ c=-a ∧ (b=a ∨ b=-a) := by
  constructor
  · rintro ⟨h,hc⟩
    have hc' : c=-a := by linarith
    refine ⟨hc', ?_⟩
    have hsq : b^2=a^2 := by rw [hc'] at h; nlinarith
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp hsq
  · rintro ⟨rfl,hb|hb⟩ <;> subst b <;> constructor <;> ring

/-- For nonnegative entries the fourth branch adds no case. This does not
justify dropping it for the signed theorem. -/
theorem booleanEasy_nonnegative_iff (a b c : ℝ)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) :
    BooleanEasy a b c ↔ a*c=b^2 ∨ b=0 ∨ a=c := by
  constructor
  · rintro (h|h|h|⟨h,hac⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl (by nlinarith [mul_nonneg ha hc]))
  · rintro (h|h|h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

end Real

section Field
variable {F : Type*} [Field F]

/-- Pivoting a symmetric rank-one interaction requires no square root and
retains either sign of the pivot. -/
theorem scalar_outer_of_pivot {n : Type*} (M : Matrix n n F) (p : n)
    (hp : M p p≠0) (hs : ∀i j,M i j=M j i)
    (hminor : ∀i j,M i j*M p p=M i p*M p j) :
    M=(M p p)⁻¹ • (fun i j => M i p*M j p) := by
  funext i j
  change M i j = (M p p)⁻¹ * (M i p*M j p)
  rw [hs j p,←hminor i j]
  field_simp [hp]

/-- The Boolean determinant-zero branch has a signed scalar rank-one
factorization whenever its first diagonal pivot is nonzero. -/
theorem boolean_rankOne_of_pivot (a b c : F) (ha : a≠0) (h : a*c=b^2) :
    booleanMatrix a b c=a⁻¹ • (fun i j => (![a,b] : Fin 2→F) i * (![a,b] : Fin 2→F) j) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [booleanMatrix,Matrix.smul_apply,smul_eq_mul]
  · field_simp
  · field_simp
  · field_simp
  · apply (mul_left_cancel₀ ha)
    rw [←mul_assoc,mul_inv_cancel₀ ha,one_mul]
    simpa [pow_two] using h

end Field
end PlanarHom.SignedThreeState
