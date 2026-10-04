import PlanarHom.DiscreteSignPartition
import Mathlib.Algebra.Polynomial.Taylor

/-! # Recursive finite-difference sign partitions for rational polynomials

At degree zero the polynomial has constant sign. At the next degree, sign
intervals for its forward difference are monotonicity intervals for the
polynomial itself; each is split by two exact binary searches. This avoids
real-root isolation entirely.
-/

noncomputable section
namespace PlanarHom.PolynomialDiscretePartition
open DiscreteSignPartition

def difference (p : Polynomial ℚ) : Polynomial ℚ := Polynomial.taylor 1 p - p

theorem eval_difference (p : Polynomial ℚ) (t : ℕ) :
    (difference p).eval (t : ℚ) = p.eval ((t+1 : ℕ) : ℚ) - p.eval (t : ℚ) := by
  simp [difference, Polynomial.taylor_apply, Polynomial.eval_comp]

theorem degree_difference_le (p : Polynomial ℚ) (d : ℕ) (hp : p.natDegree ≤ d+1) :
    (difference p).natDegree ≤ d := by
  by_cases hz : p = 0
  · simp [hz, difference]
  by_cases hd : difference p = 0
  · simp [hd]
  have ht : Polynomial.taylor 1 p ≠ 0 := (Polynomial.taylor_eq_zero 1 p).not.mpr hz
  have h := Polynomial.degree_sub_lt (Polynomial.degree_taylor p 1) ht
    (Polynomial.leadingCoeff_taylor (r:=1) (f:=p))
  rw [Polynomial.degree_taylor] at h
  change (difference p).degree < p.degree at h
  rw [Polynomial.degree_eq_natDegree hd, Polynomial.degree_eq_natDegree hz] at h
  have hh : (difference p).natDegree < p.natDegree := WithBot.coe_lt_coe.mp h
  omega

def values (p : Polynomial ℚ) (t : ℕ) : ℚ := p.eval (t : ℚ)

def oriented (p : Polynomial ℚ) (l : ℕ) : ℕ → ℚ :=
  if 0 ≤ values (difference p) l then values p else fun t => -(values p t)

theorem increasing_of_difference (p : Polynomial ℚ) (l h : ℕ)
    (hp : ∀ t, l ≤ t → t < h → 0 ≤ values (difference p) t) :
    MonotoneOn (values p) (Set.Ico l h) := by
  apply monotoneOn_of_le_succ (Set.ordConnected_Ico)
  intro t _ ht ht'
  have he := hp t ht.1 ht.2
  dsimp only [values] at he ⊢
  rw [eval_difference] at he
  exact sub_nonneg.mp he

theorem decreasing_of_difference (p : Polynomial ℚ) (l h : ℕ)
    (hp : ∀ t, l ≤ t → t < h → values (difference p) t ≤ 0) :
    MonotoneOn (fun t => -(values p t)) (Set.Ico l h) := by
  apply monotoneOn_of_le_succ (Set.ordConnected_Ico)
  intro t _ ht ht'
  have he := hp t ht.1 ht.2
  dsimp only [values] at he ⊢
  rw [eval_difference] at he
  exact neg_le_neg (sub_nonpos.mp he)

theorem oriented_increasing (p : Polynomial ℚ) (l h : ℕ)
    (hc : SignConstant (values (difference p)) (l,h)) :
    MonotoneOn (oriented p l) (Set.Ico l h) := by
  by_cases hlt : l < h
  · unfold oriented
    split_ifs with ht
    · apply increasing_of_difference
      rcases hc with hc | hc | hc
      · have := hc l le_rfl hlt; linarith
      · intro t hl hh; exact (hc t hl hh).ge
      · intro t hl hh; exact (hc t hl hh).le
    · apply decreasing_of_difference
      rcases hc with hc | hc | hc
      · intro t hl hh; exact (hc t hl hh).le
      · have := hc l le_rfl hlt; exact (ht (by linarith)).elim
      · have := hc l le_rfl hlt; exact (ht (by linarith)).elim
  · intro a ha b hb hab
    have := ha.1
    have := ha.2
    omega

theorem signConstant_of_oriented (p : Polynomial ℚ) (l : ℕ) (I : Interval)
    (hc : SignConstant (oriented p l) I) : SignConstant (values p) I := by
  unfold oriented at hc
  split_ifs at hc with ht
  · exact hc
  · rcases hc with hc | hc | hc
    · right; right
      intro t hl hh
      have := hc t hl hh
      linarith
    · right; left
      intro t hl hh
      have := hc t hl hh
      linarith
    · left
      intro t hl hh
      have := hc t hl hh
      linarith

def split (p : Polynomial ℚ) (I : Interval) : List Interval :=
  splitIncreasing (oriented p I.1) I.1 I.2

def partition : ℕ → Polynomial ℚ → ℕ → ℕ → List Interval
  | 0, _, l, h => [(l,h)]
  | d+1, p, l, h => (partition d (difference p) l h).flatMap (split p)

theorem partition_bounds (d : ℕ) (p : Polynomial ℚ) (hp : p.natDegree ≤ d)
    (l h : ℕ) (hlh : l ≤ h) :
    (∀ I ∈ partition d p l h, l ≤ I.1 ∧ I.1 ≤ I.2 ∧ I.2 ≤ h) ∧
    (∀ I ∈ partition d p l h, SignConstant (values p) I) ∧
    (∀ t, l ≤ t → t < h → ∃ I ∈ partition d p l h, I.1 ≤ t ∧ t < I.2) := by
  induction d generalizing p with
  | zero =>
    have he : p = Polynomial.C (p.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero (by omega)
    have hev (t : ℕ) : values p t = p.coeff 0 := by
      unfold values
      conv_lhs => rw [he]
      rw [Polynomial.eval_C]
    refine ⟨?_, ?_, ?_⟩
    · intro I hI
      have hi : I = (l,h) := by simpa [partition] using hI
      subst I
      exact ⟨le_rfl, hlh, le_rfl⟩
    · intro I hI
      rcases lt_trichotomy (p.coeff 0) 0 with hn | hz | hp'
      · left; intro t _ _; rw [hev]; exact hn
      · right; left; intro t _ _; rw [hev]; exact hz
      · right; right; intro t _ _; rw [hev]; exact hp'
    · intro t ht ht'
      exact ⟨(l,h), by simp [partition], ht, ht'⟩
  | succ d ih =>
    obtain ⟨hb, hs, hv⟩ := ih (difference p) (degree_difference_le p d hp)
    have hmono (I : Interval) (hI : I ∈ partition d (difference p) l h) :=
      oriented_increasing p I.1 I.2 (hs I hI)
    refine ⟨?_, ?_, ?_⟩
    · intro I hI
      obtain ⟨J, hJ, hIJ⟩ := List.mem_flatMap.mp hI
      have hJb := hb J hJ
      have hi := splitIncreasing_bounds (oriented p J.1) J.1 J.2 hJb.2.1 (hmono J hJ) I hIJ
      exact ⟨hJb.1.trans hi.1, hi.2.1, hi.2.2.trans hJb.2.2⟩
    · intro I hI
      obtain ⟨J, hJ, hIJ⟩ := List.mem_flatMap.mp hI
      have hJb := hb J hJ
      exact signConstant_of_oriented p J.1 I
        (splitIncreasing_sign _ _ _ hJb.2.1 (hmono J hJ) I hIJ)
    · intro t ht ht'
      obtain ⟨J, hJ, htJ, htJ'⟩ := hv t ht ht'
      obtain ⟨I, hI, htI, htI'⟩ := splitIncreasing_cover (oriented p J.1) J.1 J.2
        (hb J hJ).2.1 (hmono J hJ) t htJ htJ'
      exact ⟨I, List.mem_flatMap.mpr ⟨J, hJ, hI⟩, htI, htI'⟩

end PlanarHom.PolynomialDiscretePartition
