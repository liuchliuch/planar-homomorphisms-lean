import PlanarHom.Moments
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

/-!
# Common weighted amplitude coordinates

This is a new proof reconstructed from the surviving consumer interface. Equal
weighted even moments identify the weight at each distinct positive amplitude;
injectivity inside each fiber then identifies the fibers themselves.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.CommonWeightedAmplitudeCoordinates

/-- Moment uniqueness on an arbitrary finite index type, including an empty one. -/
theorem finite_type_moment_unique {I : Type*} [Fintype I]
    {node a b : I → ℝ} (hinj : Function.Injective node)
    (h : ∀ m : ℕ, (∑ i, a i * node i ^ m) = ∑ i, b i * node i ^ m) : a = b := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have he : (fun j => a (e j)) = (fun j => b (e j)) := by
    apply PlanarHom.finite_moment_unique (hinj.comp e.injective)
    intro t
    simpa only [Function.comp_apply] using
      (e.sum_comp (fun i => a i * node i ^ t.val)).trans
        ((h t.val).trans (e.sum_comp (fun i => b i * node i ^ t.val)).symm)
  funext i
  simpa only [e.apply_symm_apply] using congrFun he (e.symm i)

/-- Equal weighted even moments give equal total weights at each amplitude.
The total is taken within a fiber; no fiber injectivity is needed here. -/
theorem fiber_coefficient_eq {X S : Type*} [Fintype X]
    (classOf : X → S) (amplitude weight : X → ℝ)
    (hmom : ∀ s t : S, ∀ m : ℕ,
      (∑ x : {x // classOf x = s}, weight x.val * amplitude x.val ^ (2*m)) =
        ∑ y : {y // classOf y = t}, weight y.val * amplitude y.val ^ (2*m))
    (s t : S) (x : X) :
    (∑ y : {y // classOf y = s}, if amplitude y.val ^ 2 = amplitude x ^ 2
      then weight y.val else 0) =
    ∑ y : {y // classOf y = t}, if amplitude y.val ^ 2 = amplitude x ^ 2
      then weight y.val else 0 := by
  let support : Finset ℝ := Finset.univ.image (fun x : X => amplitude x ^ 2)
  let I := {r : ℝ // r ∈ support}
  let coeff (s : S) (r : I) : ℝ :=
    ∑ y : {y // classOf y = s}, if amplitude y.val ^ 2 = r.val then weight y.val else 0
  have hsum (s : S) (m : ℕ) :
      (∑ r : I, coeff s r * r.val ^ m) =
        ∑ y : {y // classOf y = s}, weight y.val * amplitude y.val ^ (2*m) := by
    simp only [coeff, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    let r : I := ⟨amplitude y.val ^ 2, Finset.mem_image.mpr ⟨y.val, Finset.mem_univ _, rfl⟩⟩
    rw [Finset.sum_eq_single r]
    · simp only [r, ↓reduceIte, ← pow_mul]
    · intro q hq hne
      have hne' : amplitude y.val ^ 2 ≠ q.val := by
        intro heq
        apply hne
        exact Subtype.ext heq.symm
      simp only [if_neg hne', zero_mul]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  have hc : coeff s = coeff t := by
    apply finite_type_moment_unique Subtype.val_injective
    intro m
    exact (hsum s m).trans ((hmom s t m).trans (hsum t m).symm)
  exact congrFun hc ⟨amplitude x ^ 2, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩

/-- Within a fiber with distinct positive amplitudes, the coefficient at a
point's squared amplitude is exactly that point's weight. -/
theorem fiber_coefficient_self {X S : Type*} [Fintype X]
    (classOf : X → S) (amplitude weight : X → ℝ)
    (hamp : ∀ x, 0 < amplitude x)
    (hinj : ∀ s : S,
      Function.Injective (fun x : {x // classOf x = s} => amplitude x.val))
    (s : S) (x : {x // classOf x = s}) :
    (∑ y : {y // classOf y = s}, if amplitude y.val ^ 2 = amplitude x.val ^ 2
      then weight y.val else 0) = weight x.val := by
  rw [Finset.sum_eq_single x]
  · simp
  · intro y hy hne
    have hne' : amplitude y.val ^ 2 ≠ amplitude x.val ^ 2 := by
      intro heq
      apply hne
      apply hinj s
      have hx := hamp x.val
      have hy := hamp y.val
      nlinarith
    exact if_neg hne'
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- Every point has a unique-amplitude counterpart in every other fiber, with
its original real weight preserved. Positivity rules out a missing point. -/
theorem exists_matching_point {X S : Type*} [Fintype X]
    (classOf : X → S) (amplitude weight : X → ℝ)
    (hamp : ∀ x, 0 < amplitude x) (hweight : ∀ x, 0 < weight x)
    (hinj : ∀ s : S,
      Function.Injective (fun x : {x // classOf x = s} => amplitude x.val))
    (hmom : ∀ s t : S, ∀ m : ℕ,
      (∑ x : {x // classOf x = s}, weight x.val * amplitude x.val ^ (2*m)) =
        ∑ y : {y // classOf y = t}, weight y.val * amplitude y.val ^ (2*m))
    (s t : S) (x : {x // classOf x = s}) :
    ∃ y : {y // classOf y = t},
      amplitude y.val = amplitude x.val ∧ weight y.val = weight x.val := by
  have hc := fiber_coefficient_eq classOf amplitude weight hmom s t x.val
  have hs := fiber_coefficient_self classOf amplitude weight hamp hinj s x
  have hex : ∃ y : {y // classOf y = t}, amplitude y.val ^ 2 = amplitude x.val ^ 2 := by
    by_contra hnone
    have hz : (∑ y : {y // classOf y = t},
        if amplitude y.val ^ 2 = amplitude x.val ^ 2 then weight y.val else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      exact if_neg (fun heq => hnone ⟨y, heq⟩)
    have hw : weight x.val = 0 := hs.symm.trans (hc.trans hz)
    exact (ne_of_gt (hweight x.val)) hw
  obtain ⟨y, hy⟩ := hex
  have hya : amplitude y.val = amplitude x.val := by
    have hx := hamp x.val
    have hy' := hamp y.val
    nlinarith
  have ht : (∑ z : {z // classOf z = t},
      if amplitude z.val ^ 2 = amplitude x.val ^ 2 then weight z.val else 0) = weight y.val := by
    simpa only [hy] using fiber_coefficient_self classOf amplitude weight hamp hinj t y
  exact ⟨y, hya, ht.symm.trans (hc.symm.trans hs)⟩

/-- Equal weighted even moments and injective positive amplitudes give an actual
weight-and-amplitude-preserving equivalence between any two fibers. -/
theorem exists_weighted_fiber_equiv {X S : Type*} [Fintype X]
    (classOf : X → S) (amplitude weight : X → ℝ)
    (hamp : ∀ x, 0 < amplitude x) (hweight : ∀ x, 0 < weight x)
    (hinj : ∀ s : S,
      Function.Injective (fun x : {x // classOf x = s} => amplitude x.val))
    (hmom : ∀ s t : S, ∀ m : ℕ,
      (∑ x : {x // classOf x = s}, weight x.val * amplitude x.val ^ (2*m)) =
        ∑ y : {y // classOf y = t}, weight y.val * amplitude y.val ^ (2*m))
    (s t : S) :
    ∃ e : {x // classOf x = s} ≃ {x // classOf x = t},
      (∀ x, amplitude (e x).val = amplitude x.val) ∧
      (∀ x, weight (e x).val = weight x.val) := by
  have hmatch := exists_matching_point classOf amplitude weight hamp hweight hinj hmom
  choose f hfA hfW using hmatch s t
  have hfi : Function.Injective f := by
    intro x y hxy
    apply hinj s
    exact (hfA x).symm.trans ((congrArg (fun z => amplitude z.val) hxy).trans (hfA y))
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, hxA, hxW⟩ := hmatch t s y
    refine ⟨x, hinj t ?_⟩
    exact (hfA x).trans hxA
  exact ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, hfA, hfW⟩

/-- Equal weighted even moments on the actual classes produce one common
positive amplitude vector, one common positive real weight vector, and a
class-respecting product coordinate bijection. No finiteness instance on the
class type is assumed: it follows from the surjection if ever needed. -/
theorem exists_common_weighted_chart {X S : Type*} [Fintype X] [Nonempty S]
    (classOf : X → S) (hsurj : Function.Surjective classOf)
    (amplitude weight : X → ℝ) (hamp : ∀ x, 0 < amplitude x)
    (hweight : ∀ x, 0 < weight x)
    (hinj : ∀ s : S,
      Function.Injective (fun x : {x // classOf x = s} => amplitude x.val))
    (hmom : ∀ s t : S, ∀ m : ℕ,
      (∑ x : {x // classOf x = s}, weight x.val * amplitude x.val ^ (2*m)) =
        ∑ y : {y // classOf y = t}, weight y.val * amplitude y.val ^ (2*m)) :
    ∃ k : ℕ, ∃ a mass : Fin k → ℝ, ∃ e : X ≃ S × Fin k,
      0 < k ∧ (∀ i, 0 < a i) ∧ (∀ i, 0 < mass i) ∧
      (∀ x, (e x).1 = classOf x) ∧
      (∀ x, amplitude x = a (e x).2) ∧
      (∀ x, weight x = mass (e x).2) := by
  let s0 : S := Classical.arbitrary S
  have hnon : Nonempty {x // classOf x = s0} := by
    obtain ⟨x, hx⟩ := hsurj s0
    exact ⟨⟨x, hx⟩⟩
  have hf := fun s =>
    exists_weighted_fiber_equiv classOf amplitude weight hamp hweight hinj hmom s s0
  choose E hEA hEW using hf
  let k := Fintype.card {x // classOf x = s0}
  let baseEnum : {x // classOf x = s0} ≃ Fin k := Fintype.equivFin _
  let a : Fin k → ℝ := fun i => amplitude (baseEnum.symm i).val
  let mass : Fin k → ℝ := fun i => weight (baseEnum.symm i).val
  let e : X ≃ S × Fin k := (Equiv.sigmaFiberEquiv classOf).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (fun s => (E s).trans baseEnum))
  refine ⟨k, a, mass, e, Fintype.card_pos_iff.mpr hnon,
    (fun i => hamp _), (fun i => hweight _), (fun x => rfl), ?_, ?_⟩
  · intro x
    change amplitude x =
      amplitude (baseEnum.symm (baseEnum (E (classOf x) ⟨x, rfl⟩))).val
    rw [baseEnum.symm_apply_apply]
    exact (hEA (classOf x) ⟨x, rfl⟩).symm
  · intro x
    change weight x =
      weight (baseEnum.symm (baseEnum (E (classOf x) ⟨x, rfl⟩))).val
    rw [baseEnum.symm_apply_apply]
    exact (hEW (classOf x) ⟨x, rfl⟩).symm

end PlanarHom.CommonWeightedAmplitudeCoordinates
