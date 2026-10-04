import PlanarHom.CliqueSizeProductIdentities
import PlanarHom.EffectivePolynomialTransfer

/-! NEW source condition 3.10(iv) for the squared Hamming distance kernel and
the literal target retaining precisely the clique factors of one size. -/
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace PlanarHom.HammingPottsProductIdentities
open HammingKernelTensor CliqueSizePolynomials CartesianGeometry
open EffectiveProductTransfer SymmetricProductIdentities

abbrev Color {d : ℕ} (sizes : Fin d → ℕ) := ∀ r, Fin (sizes r)

def squareFamily {d : ℕ} (sizes : Fin d → ℕ) (t : ℝ) : Matrix (Color sizes) (Color sizes) ℝ :=
  let E := EntropyCompletion.distanceKernel (hammingGraph (fun r => Fin (sizes r))) t
  E * E

def target {d : ℕ} (sizes : Fin d → ℕ) (s : ℕ) : Matrix (Color sizes) (Color sizes) ℝ :=
  fun u v => ∏ r, if sizes r=s ∧ u r=v r then 2 else 1

theorem squareFamily_entry {d : ℕ} (sizes : Fin d → ℕ) (t : ℝ) (u v : Color sizes) :
    squareFamily sizes t u v =
      ∏ r, (entry (sizes r) (decide (u r=v r))).eval t := by
  unfold squareFamily
  rw [distanceKernel_eq_tensor, tensor_mul]
  unfold tensor
  apply Finset.prod_congr rfl
  intro r _
  change ((cliqueKernel t : Matrix (Fin (sizes r)) (Fin (sizes r)) ℝ) *
    (cliqueKernel t : Matrix (Fin (sizes r)) (Fin (sizes r)) ℝ)) (u r) (v r) = _
  rw [cliqueKernel_square]
  by_cases h : u r=v r <;> simp [entry, diagonal, offDiagonal, h] <;> ring

theorem squareFamily_symmetric {d : ℕ} (sizes : Fin d → ℕ) (t : ℝ)
    (u v : Color sizes) : squareFamily sizes t u v = squareFamily sizes t v u := by
  simp only [squareFamily_entry, eq_comm]

theorem target_symmetric {d : ℕ} (sizes : Fin d → ℕ) (s : ℕ)
    (u v : Color sizes) : target sizes s u v = target sizes s v u := by
  simp only [target, eq_comm]

theorem squareFamily_positive {d : ℕ} (sizes : Fin d → ℕ)
    (hsizes : ∀ r, 2 ≤ sizes r) {t : ℝ} (ht : 0<t) (u v : Color sizes) :
    0 < squareFamily sizes t u v := by
  letI : Nonempty (Color sizes) := ⟨fun r => ⟨0, by have := hsizes r; omega⟩⟩
  unfold squareFamily
  rw [Matrix.mul_apply]
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro z _
  exact mul_pos (pow_pos ht _) (pow_pos ht _)

theorem target_product {d : ℕ} (sizes : Fin d → ℕ) (s : ℕ)
    {I : Type*} [Fintype I] (e : I → Color sizes × Color sizes) :
    (∏ i, target sizes s (e i).1 (e i).2) =
      (2:ℝ) ^ selectedCount s (fun p : I × Fin d => sizes p.2)
        (fun p => decide ((e p.1).1 p.2=(e p.1).2 p.2)) := by
  simp only [target, selectedCount]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro r _
  by_cases h : sizes r=s ∧ (e i).1 r=(e i).2 r <;> simp_all

theorem products_eq_of_square_products {d : ℕ} (sizes : Fin d → ℕ)
    (hsizes : ∀ r, 2 ≤ sizes r) {s : ℕ} (hs : 2 ≤ s)
    {I J : Type*} [Fintype I] [Fintype J]
    (e : I → Color sizes × Color sizes) (f : J → Color sizes × Color sizes)
    (h : ∀ t : ℝ, (∏ i, squareFamily sizes t (e i).1 (e i).2) =
      ∏ j, squareFamily sizes t (f j).1 (f j).2) :
    (∏ i, target sizes s (e i).1 (e i).2) = ∏ j, target sizes s (f j).1 (f j).2 := by
  rw [target_product, target_product]
  congr 1
  apply selectedCount_eq_of_function_products hs
    (fun p : I × Fin d => sizes p.2) (fun p => hsizes p.2)
    (fun p => decide ((e p.1).1 p.2=(e p.1).2 p.2))
    (fun p : J × Fin d => sizes p.2) (fun p => hsizes p.2)
    (fun p => decide ((f p.1).1 p.2=(f p.1).2 p.2))
  intro t
  simpa only [squareFamily_entry, Fintype.prod_prod_type] using h t

/-- The actual upper-triangular finite-alphabet product condition, after any
fixed source color-coordinate equivalence. No target identity is assumed. -/
theorem productIdentities {q d : ℕ} (sizes : Fin d → ℕ) (hsizes : ∀ r, 2 ≤ sizes r)
    {s : ℕ} (hs : 2 ≤ s) (e : Fin q ≃ Color sizes) :
    ProductIdentities (fun t i j => squareFamily sizes t (e i) (e j))
      (fun i j => target sizes s (e i) (e j)) := by
  intro m hm a b ha hb h
  let ea : (Σ u : Upper q, Fin (a u)) → Color sizes × Color sizes :=
    fun k => (e k.1.val.1, e k.1.val.2)
  let eb : (Σ u : Upper q, Fin (b u)) → Color sizes × Color sizes :=
    fun k => (e k.1.val.1, e k.1.val.2)
  have hp : ∀ t : ℝ, (∏ k, squareFamily sizes t (ea k).1 (ea k).2) =
      ∏ k, squareFamily sizes t (eb k).1 (eb k).2 := by
    intro t
    simpa only [ea, eb, Fintype.prod_sigma, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using congrFun h t
  have ht := products_eq_of_square_products sizes hsizes hs ea eb hp
  simpa only [ea, eb, Fintype.prod_sigma, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using ht

end PlanarHom.HammingPottsProductIdentities
