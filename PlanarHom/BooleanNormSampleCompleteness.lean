import PlanarHom.BooleanNormSampleMachines
import PlanarHom.BooleanFieldNormSamples

/-! The concrete norm-filter machine retains enough rational samples, directly
from the nonzero polynomial certificates, and therefore separates all counts. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanNormSampleCompleteness
open BooleanNormSampleSearch BooleanNormSampleMachines BooleanFieldNormSamples
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {b : ℕ}

abbrev FamilyIndex (b : ℕ) (p : Input) := Fin (ExponentVectors.box b p.2.1).length

def countFamily (p : Input) (v : FamilyIndex b p) (i : Fin b) : ℕ :=
  min (counts p i) (((ExponentVectors.box b p.2.1).get v).getD i.val 0)

theorem countFamily_le (p : Input) (v : FamilyIndex b p) (i : Fin b) :
    countFamily p v i ≤ counts p i := Nat.min_le_left _ _

theorem mem_candidates_iff_norm (f : K →+* ℝ) (c a w : Fin b → K) (p : Input) (q : ℚ) :
    q ∈ BooleanNormSampleMachines.candidates c a w p ↔
      q ∈ BooleanExceptionalGrid.rationalGrid p.1 ∧
        NormSeparates f c a w (counts p) (countFamily p) q := by
  rw [BooleanNormSampleMachines.mem_candidates_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h i j hij
    let ki := (ExponentVectors.box b p.2.1).get i
    let kj := (ExponentVectors.box b p.2.1).get j
    have hm : (ki,kj) ∈ pairs b p := (mem_pairs_iff b p _).mpr
      ⟨List.get_mem _ _,List.get_mem _ _⟩
    have hel : eligible a p (ki,kj) := by
      obtain ⟨g,hag,hkg⟩ := hij
      refine ⟨g,?_,hkg⟩
      intro ha
      exact hag (by rw [ha,f.map_zero])
    exact h (ki,kj) hm hel
  · intro h kl hkl hel
    rcases kl with ⟨k,l⟩
    obtain ⟨hk,hl⟩ := (mem_pairs_iff b p _).mp hkl
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hk
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hl
    have hij : ∃ g, f (a g) ≠ 0 ∧ countFamily p i g ≠ countFamily p j g := by
      obtain ⟨g,hag,hkg⟩ := hel
      refine ⟨g,?_,?_⟩
      · intro ha
        exact hag (f.injective (ha.trans f.map_zero.symm))
      · simpa only [countFamily,hi,hj] using hkg
    have hki : countFamily p i = leftCounts p (k,l) := by
      funext g
      simp only [countFamily,hi,leftCounts]
    have hlj : countFamily p j = rightCounts p (k,l) := by
      funext g
      simp only [countFamily,hj,rightCounts]
    simpa only [normValue_eq,hki,hlj] using h i j hij

theorem candidates_toFinset (f : K →+* ℝ) (c a w : Fin b → K) (p : Input) :
    (BooleanNormSampleMachines.candidates c a w p).toFinset =
      (BooleanExceptionalGrid.rationalGrid p.1).filter
        (NormSeparates f c a w (counts p) (countFamily p)) := by
  ext q
  simp only [List.mem_toFinset,mem_candidates_iff_norm f,Finset.mem_filter]

/-- A direct count for the samples retained by the executable norm predicate. -/
theorem length_candidates_ge (f : K →+* ℝ) (c a w : Fin b → K)
    (p : Input) (B L : ℕ) (hN : p.1=B+L)
    (hB : BooleanExceptionalSampling.exceptionalBound (FamilyIndex b p) (counts (b := b) p) ≤ B)
    (hp : BooleanExceptionalSource.SeparatedParameters
      (fun g => f (c g)) (fun g => f (a g)) (fun g => f (w g))) :
    L ≤ (BooleanNormSampleMachines.candidates c a w p).length := by
  have h := normGrid_card_ge_of_bound f c a w (counts p) (countFamily p) B L hB hp
    (countFamily_le p)
  rw [← hN,← candidates_toFinset f c a w p] at h
  exact h.trans (List.toFinset_card_le _)

def budget (b M : ℕ) : ℕ := ((M+1)^b)^2 * (2^b*(b*M))

/-- The enumeration bound is an explicit polynomial in the unary cap. -/
theorem exceptionalBound_le_budget (p : Input) :
    BooleanExceptionalSampling.exceptionalBound (FamilyIndex b p) (counts (b := b) p) ≤ budget b p.2.1 := by
  have hs : ∑ i : Fin b, counts p i ≤ b*p.2.1 := by
    calc
      _ ≤ ∑ _i : Fin b, p.2.1 := Finset.sum_le_sum (fun _ _ => Nat.min_le_left _ _)
      _ = _ := by simp
  simp only [BooleanExceptionalSampling.exceptionalBound,FamilyIndex,Fintype.card_fin,
    ExponentVectors.length_box,BooleanExceptionalSampling.degreeBound,budget]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hs)

theorem length_candidates_ge_budget (f : K →+* ℝ) (c a w : Fin b → K)
    (p : Input) (L : ℕ) (hN : p.1=budget b p.2.1+L)
    (hp : BooleanExceptionalSource.SeparatedParameters
      (fun g => f (c g)) (fun g => f (a g)) (fun g => f (w g))) :
    L ≤ (BooleanNormSampleMachines.candidates c a w p).length :=
  length_candidates_ge f c a w p (budget b p.2.1) L hN (exceptionalBound_le_budget p) hp

/-- Every returned point has the source's real separation property. -/
theorem candidate_separates (f : K →+* ℝ) (c a w : Fin b → K) (p : Input) (q : ℚ)
    (hq : q ∈ BooleanNormSampleMachines.candidates c a w p) :
    BooleanExceptionalSampling.SeparatesUnequalCounts
      (fun g => f (c g)) (fun g => f (a g)) (fun g => f (w g))
      (counts p) (countFamily p) (q : ℝ) :=
  ((mem_candidates_iff_norm f c a w p q).mp hq).2.separates

theorem ofFn_mem_box (p : Input) (k : Fin b → ℕ) (hk : ∀ i, k i ≤ counts p i) :
    List.ofFn k ∈ ExponentVectors.box b p.2.1 := by
  apply (ExponentVectors.mem_box b p.2.1 _).mpr
  refine ⟨by simp,?_⟩
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact (hk i).trans (Nat.min_le_left _ _)

theorem clipped_ofFn_eq (p : Input) (k : Fin b → ℕ) (hk : ∀ i, k i ≤ counts p i) :
    (fun i : Fin b => min (counts p i) ((List.ofFn k).getD i.val 0)) = k := by
  funext i
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
  simpa only [List.getElem_ofFn] using min_eq_right (hk i)

/-- Enumeration covers every honest pair of bounded count vectors, so no
source product is missed by the literal list implementation. -/
theorem candidate_norm_ne_zero (c a w : Fin b → K) (p : Input) (q : ℚ)
    (hq : q ∈ BooleanNormSampleMachines.candidates c a w p)
    (k l : Fin b → ℕ) (hk : ∀ i, k i ≤ counts p i) (hl : ∀ i, l i ≤ counts p i)
    (hdiff : ∃ i, a i ≠ 0 ∧ k i ≠ l i) :
    BooleanFieldCollision.collision c a w (algebraMap ℚ K q) (counts p) k l ≠ 0 := by
  let kl : CountPair := (List.ofFn k,List.ofFn l)
  have hmem : kl ∈ pairs b p := (mem_pairs_iff b p kl).mpr
    ⟨ofFn_mem_box p k hk,ofFn_mem_box p l hl⟩
  have hleft : leftCounts p kl = k := clipped_ofFn_eq p k hk
  have hright : rightCounts p kl = l := clipped_ofFn_eq p l hl
  have he : eligible a p kl := by simpa only [eligible,hleft,hright] using hdiff
  have hn := (BooleanNormSampleMachines.mem_candidates_iff c a w p q).mp hq
  simpa only [normValue_eq,hleft,hright] using hn.2 kl hmem he

theorem candidate_normSeparates {I : Type*} (f : K →+* ℝ) (c a w : Fin b → K)
    (p : Input) (q : ℚ) (hq : q ∈ BooleanNormSampleMachines.candidates c a w p)
    (k : I → Fin b → ℕ) (hk : ∀ i g, k i g ≤ counts p g) :
    NormSeparates f c a w (counts p) k q := by
  intro i j hij
  apply candidate_norm_ne_zero c a w p q hq (k i) (k j) (hk i) (hk j)
  obtain ⟨g,hag,hkg⟩ := hij
  refine ⟨g,?_,hkg⟩
  intro ha
  exact hag (by rw [ha,f.map_zero])

/-- The returned sample separates every bounded source family, independently
of how that family was indexed before the machine enumerated its box. -/
theorem candidate_separates_bounded {I : Type*} (f : K →+* ℝ) (c a w : Fin b → K)
    (p : Input) (q : ℚ) (hq : q ∈ BooleanNormSampleMachines.candidates c a w p)
    (k : I → Fin b → ℕ) (hk : ∀ i g, k i g ≤ counts p g) :
    BooleanExceptionalSampling.SeparatesUnequalCounts
      (fun g => f (c g)) (fun g => f (a g)) (fun g => f (w g)) (counts p) k (q : ℝ) :=
  (candidate_normSeparates f c a w p q hq k hk).separates

/-- Canonical rational numerator/denominator bounds for every retained point. -/
theorem candidate_bounds (c a w : Fin b → K) (p : Input) (q : ℚ)
    (hq : q ∈ BooleanNormSampleMachines.candidates c a w p) :
    (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 ∧
      0 < q.num ∧ q.num.natAbs ≤ p.1 ∧ 0 < q.den ∧ q.den ≤ p.1+1 := by
  have hg := ((BooleanNormSampleMachines.mem_candidates_iff c a w p q).mp hq).1
  exact BooleanExceptionalGrid.subgrid_sample_bounds (fun _ h => h) hg

theorem search_mem (c a w : Fin b → K) (p : Input)
    (hpos : 0 < (BooleanNormSampleMachines.candidates c a w p).length) :
    BooleanNormSampleMachines.search c a w p ∈ BooleanNormSampleMachines.candidates c a w p := by
  change (BooleanNormSampleMachines.candidates c a w p).headD 0 ∈ _
  cases hl : BooleanNormSampleMachines.candidates c a w p with
  | nil => simp [hl] at hpos
  | cons x xs => simp

end PlanarHom.BooleanNormSampleCompleteness
