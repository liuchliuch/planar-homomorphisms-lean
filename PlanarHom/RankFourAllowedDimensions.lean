import PlanarHom.MainStructuralSupportTransport
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! Full row rank removes every repeated amplitude coordinate in an allowed
block. These are genuine finite-dimensional obstructions, before specializing
the color cardinality to four. -/
noncomputable section
open Classical
namespace PlanarHom.RankFour
open Structures Boolean
variable {C : Type} [Fintype C]

theorem rows_independent {M : Matrix C C ℝ} (h : M.rank = Fintype.card C) :
    LinearIndependent ℝ M := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  simpa only [Matrix.rank_eq_finrank_span_row, Matrix.row] using h.symm

theorem positive_amplitude_size {M : Matrix C C ℝ}
    (h : LinearIndependent ℝ M) {k d : ℕ} (hk : 0<k)
    (a : Fin k → ℝ) (ρ : Fin d → ℝ) (ha : ∀i,0<a i)
    (e : C≃Fin k×Cube d)
    (hm : ∀i j,M i j=a (e i).1*a (e j).1*tensor ρ (e i).2 (e j).2) : k=1 := by
  have hi : ∀i j : Fin k,i=j := by
    intro i j
    let x : Cube d := fun _=>false
    have he : e.symm (i,x)=e.symm (j,x) := by
      apply h.eq_of_smul_apply_eq_smul_apply (a j) (a i) _ _ (ne_of_gt (ha j))
      funext v
      simp only [Pi.smul_apply,smul_eq_mul,hm,Equiv.apply_symm_apply]
      ring
    exact congrArg Prod.fst (e.symm.injective he)
  have hk' : k≤1 := by
    by_contra hn
    have h2 : 1<k := by omega
    have he := congrArg Fin.val (hi ⟨0,hk⟩ ⟨1,h2⟩)
    simp at he
  omega

theorem bipartite_amplitude_sizes {M : Matrix C C ℝ}
    (h : LinearIndependent ℝ M) {k l d : ℕ} (hk : 0<k) (hl : 0<l)
    (a : Fin k → ℝ) (b : Fin l→ℝ) (ρ : Fin d → ℝ)
    (ha : ∀i,0<a i) (hb : ∀i,0<b i)
    (e : C≃(Fin k⊕Fin l)×Cube d)
    (hm : ∀i j,M i j=bipartiteAmplitude a b (e i).1 (e j).1*tensor ρ (e i).2 (e j).2) :
    k=1 ∧ l=1 := by
  have hi : ∀i j : Fin k,i=j := by
    intro i j
    let x : Cube d := fun _=>false
    have he : e.symm (.inl i,x)=e.symm (.inl j,x) := by
      apply h.eq_of_smul_apply_eq_smul_apply (a j) (a i) _ _ (ne_of_gt (ha j))
      funext v
      simp only [Pi.smul_apply,smul_eq_mul,hm,Equiv.apply_symm_apply]
      cases (e v).1 <;> simp only [bipartiteAmplitude] <;> ring
    exact Sum.inl.inj (congrArg Prod.fst (e.symm.injective he))
  have hj : ∀i j : Fin l,i=j := by
    intro i j
    let x : Cube d := fun _=>false
    have he : e.symm (.inr i,x)=e.symm (.inr j,x) := by
      apply h.eq_of_smul_apply_eq_smul_apply (b j) (b i) _ _ (ne_of_gt (hb j))
      funext v
      simp only [Pi.smul_apply,smul_eq_mul,hm,Equiv.apply_symm_apply]
      cases (e v).1 <;> simp only [bipartiteAmplitude] <;> ring
    exact Sum.inr.inj (congrArg Prod.fst (e.symm.injective he))
  constructor
  · by_contra hn
    have h2 : 1<k := by omega
    have he := congrArg Fin.val (hi ⟨0,hk⟩ ⟨1,h2⟩)
    simp at he
  · by_contra hn
    have h2 : 1<l := by omega
    have he := congrArg Fin.val (hj ⟨0,hl⟩ ⟨1,h2⟩)
    simp at he

theorem pow_two_eq_four {d : ℕ} (h : 2^d=4) : d=2 := by
  exact Nat.pow_right_injective (by omega : 2≤2) (show 2^d=2^2 from h)

theorem twice_pow_two_eq_four {d : ℕ} (h : 2*2^d=4) : d=1 := by
  have hp : 2^d=2 := by omega
  exact Nat.pow_right_injective (by omega : 2≤2) (show 2^d=2^1 from hp)

end PlanarHom.RankFour
