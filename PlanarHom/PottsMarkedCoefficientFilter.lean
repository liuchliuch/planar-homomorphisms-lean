import PlanarHom.PottsCenteredLeafCancellation
import PlanarHom.PottsCenteredSeriesLaw

/-! NEW reconstruction: exact exponent separation for marked long edges.
After the proved series substitution, choosing an exponent larger than the
number of short occurrences forces every long occurrence in the coefficient. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PottsCentered
open MultiGraph Polynomial
variable {V E : Type} [Fintype V] [Fintype E]

def markedExponent (long : Finset E) (N : ℕ) (A : Finset E) : ℕ :=
  N*(A∩long).card+(A\long).card

def markedPolynomial (G : MultiGraph V E) (q : ℕ) (long : Finset E) (N : ℕ) : Polynomial ℚ :=
  C ((q:ℚ)⁻¹^Fintype.card V)*∑ σ : V → Fin q,
    ∏ e : E,(1+X^(if e∈long then N else 1)*C (interaction q (σ (G.src e)) (σ (G.dst e))))

theorem sum_marked_weights (long : Finset E) (N : ℕ) (A : Finset E) :
    (∑ e∈A,if e∈long then N else 1)=markedExponent long N A := by
  rw [Finset.sum_ite]
  simp [markedExponent,Finset.filter_mem_eq_inter,Finset.sdiff_eq_filter,Nat.mul_comm]

theorem markedPolynomial_eq_subsets (G : MultiGraph V E) (q : ℕ) (long : Finset E) (N : ℕ) :
    markedPolynomial G q long N=
      ∑ A : Finset E,C (selectedValue G q A)*X^(markedExponent long N A) := by
  apply Polynomial.funext
  intro x
  simp only [markedPolynomial,eval_mul,eval_C,eval_finset_sum,eval_prod,eval_add,eval_one,eval_pow,eval_X]
  simp_rw [add_comm (1:ℚ),Finset.prod_add_one]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum,sum_marked_weights]
  rw [← Finset.mul_sum]
  dsimp [selectedValue]
  ring

theorem marked_coefficient_subsets (G : MultiGraph V E) (q : ℕ) (long : Finset E) (N d : ℕ) :
    (markedPolynomial G q long N).coeff d=
      ∑ A : Finset E,if markedExponent long N A=d then selectedValue G q A else 0 := by
  rw [markedPolynomial_eq_subsets,finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro A _
  simp [coeff_C_mul,coeff_X_pow,eq_comm]

/-- A literal subset has the selected coefficient exponent exactly when all
long occurrences are present and precisely d short occurrences are selected. -/
theorem markedExponent_eq_iff (long : Finset E) (N d : ℕ)
    (hN : (Finset.univ\long).card<N) (A : Finset E) :
    markedExponent long N A=N*long.card+d ↔ long⊆A ∧ (A\long).card=d := by
  have ha : (A∩long).card≤long.card := Finset.card_le_card Finset.inter_subset_right
  have hb : (A\long).card≤(Finset.univ\long).card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ A) (Finset.Subset.refl _))
  constructor
  · intro he
    have hc : (A∩long).card=long.card := by
      by_contra hh
      have hi : (A∩long).card+1≤long.card := by omega
      have hm := Nat.mul_le_mul_left N hi
      dsimp [markedExponent] at he
      nlinarith
    have hset : A∩long=long := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    refine ⟨?_,?_⟩
    · rw [← hset]
      exact Finset.inter_subset_left
    · dsimp [markedExponent] at he
      rw [hc] at he
      omega
  · rintro ⟨hsub,hcard⟩
    simp [markedExponent,Finset.inter_eq_right.mpr hsub,hcard]

/-- The true marked polynomial coefficient filters long paths with no
hypothesis about which subsets were selected by an oracle. -/
theorem marked_coefficient_filter (G : MultiGraph V E) (q : ℕ) (long : Finset E)
    (N d : ℕ) (hN : (Finset.univ\long).card<N) :
    (markedPolynomial G q long N).coeff (N*long.card+d)=
      ∑ A : Finset E,if long⊆A ∧ (A\long).card=d then selectedValue G q A else 0 := by
  rw [marked_coefficient_subsets]
  simp_rw [markedExponent_eq_iff long N d hN]
end PlanarHom.PottsCentered
