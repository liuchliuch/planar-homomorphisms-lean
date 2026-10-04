import PlanarHom.ExponentialZeros
import PlanarHom.RealSpectralInterpolation
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Actual spectral products lie in a finite span with stars-and-bars dimension.
This supplies the exponential-family zero bound in source Lemma 3.10. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.SpectralProductZeros

variable {s : ℕ}

def base (μ : Fin s → ℝ) {m : ℕ} (u : Sym (Fin s) m) : ℝ :=
  (u.val.map μ).prod

def powerSpan (μ : Fin s → ℝ) (m : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ (Set.range fun u : Sym (Fin s) m => fun t : ℝ => base μ u ^ t)

@[simp] theorem base_cons (μ : Fin s → ℝ) {m : ℕ} (i : Fin s) (u : Sym (Fin s) m) :
    base μ (Sym.cons i u) = μ i * base μ u := by
  simp [base, Sym.cons]

theorem base_pos (μ : Fin s → ℝ) (hμ : ∀ i, 0 < μ i)
    {m : ℕ} (u : Sym (Fin s) m) : 0 < base μ u := by
  change 0 < (u.val.map μ).prod
  induction u.val using Multiset.induction_on with
  | empty => simp
  | @cons i l ih => simpa using mul_pos (hμ i) ih

/-- Multiplication by one eigenvalue power increases the exact factor count by one. -/
theorem generator_mul_mem (μ : Fin s → ℝ) (hμ : ∀ i, 0 < μ i)
    {m : ℕ} (i : Fin s) {f : ℝ → ℝ} (hf : f ∈ powerSpan μ m) :
    (fun t => μ i ^ t * f t) ∈ powerSpan μ (m + 1) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    have he : (fun t : ℝ => μ i ^ t * base μ u ^ t) =
        (fun t : ℝ => base μ (Sym.cons i u) ^ t) := by
      funext t
      rw [base_cons, Real.mul_rpow (le_of_lt (hμ i)) (le_of_lt (base_pos μ hμ u))]
    rw [he]
    exact Submodule.subset_span ⟨Sym.cons i u, rfl⟩
  | zero =>
    simp only [Pi.zero_apply, mul_zero]
    exact (powerSpan μ (m + 1)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [Pi.add_apply, mul_add] using (powerSpan μ (m + 1)).add_mem ihx ihy
  | smul c x hx ih =>
    convert (powerSpan μ (m + 1)).smul_mem c ih using 1
    ext t
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- An arbitrary product of m spectral sums belongs to the same m-factor span.
Its coefficients are unrestricted signed real numbers. -/
theorem product_mem_powerSpan {E : Type*} (μ : Fin s → ℝ) (hμ : ∀ i, 0 < μ i)
    (c : E → Fin s → ℝ) (word : List E) :
    (fun t : ℝ => (word.map fun e => ∑ i, c e i * μ i ^ t).prod) ∈
      powerSpan μ word.length := by
  induction word with
  | nil =>
    have h : (fun _ : ℝ => (1 : ℝ)) ∈ powerSpan μ 0 := by
      have hh := Submodule.subset_span (R := ℝ)
        (s := Set.range fun u : Sym (Fin s) 0 => fun t : ℝ => base μ u ^ t)
        (Set.mem_range_self (Sym.nil : Sym (Fin s) 0))
      simpa [base, Sym.nil] using hh
    simpa using h
  | cons e word ih =>
    have he : (fun t : ℝ => ((e :: word).map fun e => ∑ i, c e i * μ i ^ t).prod) =
        ∑ i, c e i • (fun t : ℝ => μ i ^ t *
          (word.map fun e => ∑ j, c e j * μ j ^ t).prod) := by
      funext t
      simp only [List.map_cons, List.prod_cons, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact (powerSpan μ (word.length + 1)).sum_mem fun i _ =>
      (powerSpan μ (word.length + 1)).smul_mem _ (generator_mul_mem μ hμ i ih)

/-- Distinct bases are merged by their numerical value before applying Lemma3.9.
The resulting count is bounded by the actual stars-and-bars cardinality. -/
theorem zero_card_le_of_mem_powerSpan (μ : Fin s → ℝ) (hμ : ∀ i, 0 < μ i)
    {m : ℕ} (f : ℝ → ℝ) (hf : f ∈ powerSpan μ m) (hne : f ≠ 0)
    (T : Finset ℝ) (hT : ∀ x ∈ T, f x = 0) :
    T.card ≤ (s + m - 1).choose m - 1 := by
  classical
  let U : Finset ℝ := Finset.univ.image (base μ (m := m))
  have hspan : f ∈ Submodule.span ℝ
      (Set.range fun u : U => fun x : ℝ => (u.val : ℝ) ^ x) := by
    apply (Submodule.span_mono (s := Set.range fun u : Sym (Fin s) m =>
      fun x : ℝ => base μ u ^ x) ?_) hf
    rintro _ ⟨u, rfl⟩
    exact ⟨⟨base μ u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩⟩, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  let e := Fintype.equivFin U
  let a : Fin (Fintype.card U) → ℝ := fun i => (e.symm i).val
  let b : Fin (Fintype.card U) → ℝ := fun i => c (e.symm i)
  have ha : ∀ i, 0 < a i := by
    intro i
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp (e.symm i).property
    change 0 < (e.symm i).val
    rw [← hu]
    exact base_pos μ hμ u
  have hinj : Function.Injective a := by
    intro i j h
    exact e.symm.injective (Subtype.ext h)
  have hrep (x : ℝ) : (∑ i, b i * a i ^ x) = f x := by
    calc
      _ = ∑ u : U, c u * (u.val : ℝ) ^ x := by
        apply Fintype.sum_equiv e.symm
        intro i
        rfl
      _ = f x := by
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hc x
  have hb : ∃ i, b i ≠ 0 := by
    by_contra! h
    apply hne
    funext x
    rw [← hrep x]
    simp [h]
  have hz : T.card < Fintype.card U := by
    apply exponentialSum_zero_finset_card_lt (fun i => Real.log (a i)) b
      (fun i j h => hinj (Real.log_injOn_pos (ha i) (ha j) h)) hb T
    intro x hx
    rw [← sum_rpow_eq_exponentialSum a b ha, hrep]
    exact hT x hx
  have hcard : Fintype.card U ≤ (s + m - 1).choose m := by
    calc
      Fintype.card U = U.card := Fintype.card_coe U
      _ ≤ Fintype.card (Sym (Fin s) m) := Finset.card_image_le
      _ = (s + m - 1).choose m := by rw [Sym.card_sym_eq_choose, Fintype.card_fin]
  omega

/-- Source (3.5), case(S), for any two products of the same number of spectral sums. -/
theorem product_agreement_card_le {E : Type*} (μ : Fin s → ℝ) (hμ : ∀ i, 0 < μ i)
    (c : E → Fin s → ℝ) (v w : List E) (hvw : v.length = w.length)
    (hne : (fun t : ℝ => (v.map fun e => ∑ i, c e i * μ i ^ t).prod) ≠
      (fun t : ℝ => (w.map fun e => ∑ i, c e i * μ i ^ t).prod))
    (T : Finset ℝ) (hT : ∀ t ∈ T,
      (v.map fun e => ∑ i, c e i * μ i ^ t).prod =
        (w.map fun e => ∑ i, c e i * μ i ^ t).prod) :
    T.card ≤ (s + v.length - 1).choose v.length - 1 := by
  let f : ℝ → ℝ := fun t =>
    (v.map fun e => ∑ i, c e i * μ i ^ t).prod -
      (w.map fun e => ∑ i, c e i * μ i ^ t).prod
  have hv := product_mem_powerSpan μ hμ c v
  have hw : (fun t : ℝ => (w.map fun e => ∑ i, c e i * μ i ^ t).prod) ∈
      powerSpan μ v.length := by rw [hvw]; exact product_mem_powerSpan μ hμ c w
  apply zero_card_le_of_mem_powerSpan μ hμ f ((powerSpan μ v.length).sub_mem hv hw)
  · intro h
    apply hne
    funext t
    exact sub_eq_zero.mp (congrFun h t)
  · intro t ht
    exact sub_eq_zero.mpr (hT t ht)

variable {C : Type} [Fintype C] [DecidableEq C]

/-- The actual source matrix family in case(S), for every real parameter. -/
def realPower (M : Matrix C C ℝ) (t : ℝ) : Matrix C C ℝ :=
  cfc (fun x : ℝ => x ^ t) M

theorem realPower_entry (M : Matrix C C ℝ) (t : ℝ) (i j : C) :
    realPower M t i j = ∑ a, RealSpectralInterpolation.projector M a i j *
      RealSpectralInterpolation.scalar M a ^ t := by
  rw [realPower, RealSpectralInterpolation.cfc_eq_sum_projectors]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Source (3.5) for genuine real matrix powers, including repeated eigenvalues.
The spectrum indexing counts distinct eigenvalues, not algebraic multiplicity. -/
theorem matrixPower_product_agreement_card_le (M : Matrix C C ℝ) (hM : M.PosDef)
    (v w : List (C × C)) (hvw : v.length = w.length)
    (hne : (fun t : ℝ => (v.map fun e => realPower M t e.1 e.2).prod) ≠
      (fun t : ℝ => (w.map fun e => realPower M t e.1 e.2).prod))
    (T : Finset ℝ) (hT : ∀ t ∈ T,
      (v.map fun e => realPower M t e.1 e.2).prod =
        (w.map fun e => realPower M t e.1 e.2).prod) :
    T.card ≤ (Nat.card (spectrum ℝ M) + v.length - 1).choose v.length - 1 := by
  apply product_agreement_card_le (RealSpectralInterpolation.scalar M)
    (RealSpectralInterpolation.scalar_pos M hM)
    (fun e : C × C => fun a => RealSpectralInterpolation.projector M a e.1 e.2) v w hvw
  · simpa only [realPower_entry] using hne
  · simpa only [realPower_entry] using hT

/-- The stars-and-bars form printed in the paper equals the product-span bound
when there is at least one distinct eigenvalue. -/
theorem choose_degree_bound_eq {s m : ℕ} (hs : 0 < s) :
    (s + m - 1).choose m - 1 = (m + s - 1).choose (s - 1) - 1 := by
  congr 1
  rw [Nat.add_comm s m]
  exact Nat.choose_symm_of_eq_add (by omega)

end PlanarHom.SpectralProductZeros
