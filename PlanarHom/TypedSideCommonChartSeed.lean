import PlanarHom.ClosedFamilySandwich
import PlanarHom.TypedContextualGadgetClosure
import PlanarHom.TypedHomogeneousSourceAccess
import PlanarHom.TensorPower
import PlanarHom.TypedMixedPhysicalAvailabilityGram

/-! Exact surviving common-chart seed proofs, with source-closed imports. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity ClosedMatrixFamily TypedSideSourceAccess
variable {x y s bt : ℕ}
theorem xFamily_entrywise_pow
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (H : Matrix (Fin x) (Fin x) ℝ) (hH : H∈xFamily F FB) (n : ℕ) (hn : 0<n) :
    (fun i j=>H i j^n)∈xFamily F FB := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  induction k with
  | zero => simpa only [Nat.zero_add,pow_one] using hH
  | succ k ih =>
    simpa only [pow_succ] using xFamily_parallel F FB (fun i j=>H i j^(k+1)) H (ih (by omega)) hH
def rowGramPower (B : Matrix (Fin x) (Fin y) ℝ) : Matrix (Fin x) (Fin x) ℝ :=
  fun i j=>(B*B.transpose) i j ^ max 1 (x-1)
theorem rowGramPower_posDef [Nonempty (Fin y)]
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀ i j,0<B i j)
    (hproj : ∀ i j,i≠j → ∀ t : ℝ,B i≠t•B j) : (rowGramPower B).PosDef := by
  have hn : ∀ i,B i≠0 := by
    intro i h
    have hz := congrFun h (Classical.arbitrary (Fin y))
    exact ne_of_gt (hB i _) hz
  have hp := hadamard_weighted_gram_posDef B (fun _=>1) (fun _=>zero_lt_one) hn hproj
  simpa only [Matrix.diagonal_one,Matrix.mul_one] using hp
theorem rowGramPower_positive [Nonempty (Fin y)]
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀ i j,0<B i j) :
    ∀ i j,0<rowGramPower B i j := by
  intro i j
  apply pow_pos
  change 0 < ∑ k : Fin y,B i k*B j k
  exact Finset.sum_pos (fun k _=>mul_pos (hB i k) (hB j k)) Finset.univ_nonempty
theorem rowGramPower_admissible [Nonempty (Fin x)] [Nonempty (Fin y)]
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀ i j,0<B i j)
    (hproj : ∀ i j,i≠j → ∀ t : ℝ,B i≠t•B j)
    (hgram : B*B.transpose∈xFamily F FB) : Admissible (xFamily F FB) (rowGramPower B) := by
  have hp := rowGramPower_posDef B hB hproj
  have hpos := rowGramPower_positive B hB
  refine ⟨xFamily_entrywise_pow F FB _ hgram _ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)),
    fun i j=>(hpos i j).le,hp,?_⟩
  exact support_connected_of_positive_entries _ hp.1 hpos
end PlanarHom.TypedBipartiteContext
