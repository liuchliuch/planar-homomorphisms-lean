import PlanarHom.UniformFieldRecoveryHeights

/-! Concrete denominator clearing and uniform heights from literal rational field presentations. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.UniformFieldPresentationHeights
open Complexity FieldCoordinateCertificates IntegerCoordinateBounds CanonicalCoordinateHeights UniformFieldHeights

/-- One coordinate for 1 and one entry for every multiplication-by-basis matrix. -/
abbrev Slot (d : ℕ) := Fin d ⊕ (Fin d × Fin d × Fin d)

/-- Explicit arithmetic slot order: unit coordinates, then multiplication indices. -/
def slotEquiv (d : ℕ) : Slot d ≃ Fin (d + d * (d*d)) :=
  (Equiv.sumCongr (Equiv.refl (Fin d))
    ((Equiv.prodCongr (Equiv.refl (Fin d)) finProdFinEquiv).trans finProdFinEquiv)).trans finSumFinEquiv

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def presentation : Slot dimension → ℚ
  | .inl i => basis.equivFun 1 i
  | .inr p => multiplicationMatrix basis (basis p.1) p.2.1 p.2.2

/-- A literal finite rational list, in the fixed equivalence-to-Fin order. -/
def presentationList : List ℚ :=
  List.ofFn (fun i : Fin (dimension + dimension * (dimension*dimension)) =>
    presentation basis ((slotEquiv dimension).symm i))

def presentationBits : ℕ := (BitEncoding.rat.list.encode (presentationList basis)).length

def denominator : ℕ := ∏ j : Slot dimension, (presentation basis j).den

def numerator (j : Slot dimension) : ℤ := (presentation basis j).num *
  ((∏ k ∈ Finset.univ.erase j, (presentation basis k).den : ℕ) : ℤ)

theorem denominator_pos : 0 < denominator basis :=
  Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun _ _ => (Rat.den_pos _).ne'))

theorem numerator_spec (j : Slot dimension) :
    (denominator basis : ℚ) * presentation basis j = numerator basis j := by
  have hp := Finset.prod_erase_mul Finset.univ (fun k => (presentation basis k).den) (Finset.mem_univ j)
  dsimp only [denominator, numerator]
  rw [← hp, Nat.cast_mul]
  conv_lhs => rhs; rw [← Rat.num_div_den (presentation basis j)]
  have hd : ((presentation basis j).den : ℚ) ≠ 0 := by exact_mod_cast (Rat.den_pos _).ne'
  push_cast
  field_simp

/-- Concrete structure data, obtained by multiplying the actual canonical rational
denominators. No chosen denominator certificate or extra height advice is supplied. -/
def cleared : ClearedCoordinates basis (fun k : Fin dimension => basis k) where
  denominator := denominator basis
  denominator_pos := denominator_pos basis
  initial := fun i => numerator basis (.inl i)
  transition := fun a i j => numerator basis (.inr (a,i,j))
  initial_spec := fun i => numerator_spec basis (.inl i)
  transition_spec := fun a i j => numerator_spec basis (.inr (a,i,j))

theorem presentation_member (j : Slot dimension) : presentation basis j ∈ presentationList basis :=
  List.mem_ofFn.mpr ⟨slotEquiv dimension j, by simp⟩

theorem slot_heights (j : Slot dimension) :
    (presentation basis j).num.natAbs ≤ 2 ^ presentationBits basis ∧
    (presentation basis j).den ≤ 2 ^ presentationBits basis := by
  have hl := MaterializedFieldHeights.element_length_le_list BitEncoding.rat (presentationList basis)
    (presentation_member basis j)
  have hb := rat_heights_le_pow_encoding_length (presentation basis j)
  exact ⟨hb.1.trans (Nat.pow_le_pow_right (by omega) hl), hb.2.trans (Nat.pow_le_pow_right (by omega) hl)⟩

theorem cleared_entry_bounds :
    (cleared basis).denominator ≤ 2 ^ (presentationBits basis * (Fintype.card (Slot dimension)+1)) ∧
    (∀ i, ((cleared basis).initial i).natAbs ≤ 2 ^ (presentationBits basis * (Fintype.card (Slot dimension)+1))) ∧
    (∀ a i j, ((cleared basis).transition a i j).natAbs ≤
      2 ^ (presentationBits basis * (Fintype.card (Slot dimension)+1))) := by
  let B := 2 ^ presentationBits basis
  have hB : 0 < B := pow_pos (by omega) _
  have hprod (s : Finset (Slot dimension)) : (∏ j ∈ s, (presentation basis j).den) ≤ B ^ s.card := by
    simpa using Finset.prod_le_prod' (s := s) (fun j _ => (slot_heights basis j).2)
  have hd : denominator basis ≤ B ^ (Fintype.card (Slot dimension)+1) :=
    (hprod Finset.univ).trans (Nat.pow_le_pow_right hB (by simp))
  have hn (j : Slot dimension) : (numerator basis j).natAbs ≤ B ^ (Fintype.card (Slot dimension)+1) := by
    rw [numerator, Int.natAbs_mul, Int.natAbs_natCast]
    calc
      _ ≤ B * B ^ (Finset.univ.erase j).card := Nat.mul_le_mul (slot_heights basis j).1 (hprod _)
      _ ≤ B * B ^ Fintype.card (Slot dimension) := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right hB (Finset.card_erase_le.trans (by simp)))
      _ = _ := (pow_succ' _ _).symm
  simpa only [cleared, B, ← pow_mul] using And.intro hd (And.intro (fun i => hn (.inl i))
    (fun a i j => hn (.inr (a,i,j))))

/-- Summing the concrete initial and transition numerators costs only a factor
bounded by the dimension; the fourth power accounts for the multiplication rows. -/
theorem growth_bound {c : ℕ} (hc : dimension ≤ c) :
    growthConstant (cleared basis) ≤ (c+1)^4 *
      2 ^ (presentationBits basis * (Fintype.card (Slot dimension)+1)) := by
  let T := 2 ^ (presentationBits basis * (Fintype.card (Slot dimension)+1))
  have hT : 1 ≤ T := Nat.one_le_pow _ _ (by omega)
  have hb := cleared_entry_bounds basis
  have hi : (∑ i, ((cleared basis).initial i).natAbs) ≤ dimension*T := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb.2.1 i)
  have ht : transitionBound (cleared basis) ≤ dimension^3*T := by
    unfold transitionBound
    calc
      _ ≤ ∑ _a : Fin dimension, ∑ _i : Fin dimension, ∑ _j : Fin dimension, T := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum (fun j _ => hb.2.2 a i j)
      _ = _ := by simp; ring
  have hd4 : dimension ≤ (c+1)^4 := hc.trans ((Nat.le_succ c).trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < c+1) (by omega : 1 ≤ 4)))
  have h4 : dimension^4 ≤ (c+1)^4 := Nat.pow_le_pow_left (by omega) _
  apply max_le
  · exact hT.trans (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _))
  · apply max_le
    · exact hi.trans (Nat.mul_le_mul_right _ hd4)
    · exact (Nat.mul_le_mul_left dimension ht).trans (by
        calc
          dimension*(dimension^3*T) = dimension^4*T := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ h4)

theorem heightConstant_bound {c : ℕ} (hc : dimension ≤ c) :
    Certificate.heightConstant (cleared basis) ≤ (c+1)^5 *
      2 ^ (presentationBits basis * (Fintype.card (Slot dimension)+1)) := by
  let T := 2 ^ (presentationBits basis * (Fintype.card (Slot dimension)+1))
  have hg := growth_bound basis hc
  have hT : 1 ≤ T := Nat.one_le_pow _ _ (by omega)
  have h45 : (c+1)^4 ≤ (c+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hT' : T ≤ (c+1)^5*T := Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)
  unfold Certificate.heightConstant
  refine max_le (hT.trans hT') (max_le ((cleared_entry_bounds basis).1.trans hT') (max_le ?_ ?_))
  · exact hg.trans (Nat.mul_le_mul_right _ h45)
  · exact (Nat.mul_le_mul (show dimension ≤ c+1 by omega) hg).trans_eq (by ring)

/-- Explicit linear exponent polynomial in presentation bits, with coefficients
that depend only on the degree cap c. -/
def presentationExponentConstant (c : ℕ) : ℕ := (c+1)^5 + (c+c^3+1)

def presentationExponentPolynomial (c : ℕ) : Polynomial ℕ := Polynomial.C (presentationExponentConstant c) * Polynomial.X

/-- The literal presentation itself supplies the structure-height budget. -/
theorem heightConstant_le_pow_presentation {c : ℕ} (hc : dimension ≤ c) :
    Certificate.heightConstant (cleared basis) ≤
      2 ^ ((presentationExponentPolynomial c).eval (presentationBits basis+1)) := by
  have hcard : Fintype.card (Slot dimension) ≤ c+c^3 := by
    simp only [Slot, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    have hp := Nat.pow_le_pow_left hc 3
    nlinarith
  have hfactor : (c+1)^5 ≤ 2^((c+1)^5) := (Nat.lt_two_pow_self).le
  calc
    _ ≤ (c+1)^5 * 2^(presentationBits basis*(Fintype.card (Slot dimension)+1)) := heightConstant_bound basis hc
    _ ≤ 2^((c+1)^5) * 2^(presentationBits basis*(c+c^3+1)) := Nat.mul_le_mul hfactor
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (by omega)))
    _ = 2^((c+1)^5 + presentationBits basis*(c+c^3+1)) := (pow_add _ _ _).symm
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by omega)
      simp only [presentationExponentPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, presentationExponentConstant]
      calc
        (c+1)^5 + presentationBits basis*(c+c^3+1) ≤
            (c+1)^5*(presentationBits basis+1) + (c+c^3+1)*(presentationBits basis+1) := by
          apply Nat.add_le_add
          · exact Nat.le_mul_of_pos_right _ (by omega)
          · rw [Nat.mul_comm (presentationBits basis)]
            exact Nat.mul_le_mul_left _ (Nat.le_succ _)
        _ = _ := (Nat.add_mul _ _ _).symm

/-- After denominator clearing is derived, presentation bits and input bits are
the only varying size parameters left in the interpolation-height polynomial. -/
def presentationOutputPolynomial (c : ℕ) : Polynomial ℕ :=
  (allHeightsPolynomial c).comp
    (Polynomial.C (presentationExponentConstant c+1) * (Polynomial.X+1))

variable [DecidableEq K]

/-- No added height hypothesis: the explicit rational presentation pays for
all total recovery output growth, uniformly over fields and bases of degree ≤c. -/
theorem recovery_encoding_bound {c : ℕ} (hc : dimension ≤ c)
    (input : MaterializedLagrangeRecoveryMachines.Data K) :
    ((numberFieldEncoding basis).encode (MaterializedLagrangeRecoveryMachines.recover input)).length ≤
      (presentationOutputPolynomial c).eval
        (((MaterializedLagrangeRecoveryMachines.inputEncoding basis).encode input).length + presentationBits basis) := by
  have hb := UniformFieldHeights.total_recovery_encoding_bound (cleared basis) hc (heightConstant_le_pow_presentation basis hc) input
  apply hb.trans
  simp only [presentationOutputPolynomial, Polynomial.eval_comp]
  apply MachineComposition.natPolynomial_monotone
  simp only [presentationExponentPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_one]
  nlinarith

end PlanarHom.UniformFieldPresentationHeights
