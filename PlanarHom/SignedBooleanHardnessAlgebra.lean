import PlanarHom.SignedThreeStateAlgebra

/-! Signed Boolean hardness normalization uses explicit planar operations:
optional terminal leaves, two-edge stretching, then twofold thickening.
This file proves all numerical preconditions for the positive biased target;
the computational gadget reduction is a separate obligation. -/
namespace PlanarHom.SignedThreeState

def leafBoolean (a b c : ℝ) : ℝ×ℝ×ℝ :=
  (a*(a+b)^2,b*(a+b)*(b+c),c*(b+c)^2)

def gramSquareBoolean (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  booleanMatrix ((a^2+b^2)^2) ((b*(a+c))^2) ((b^2+c^2)^2)

theorem gramSquareBoolean_eq (a b c : ℝ) :
    gramSquareBoolean a b c=schurSquare (booleanMatrix a b c*booleanMatrix a b c) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramSquareBoolean,schurSquare,booleanMatrix,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem gramSquareBoolean_det (a b c : ℝ) :
    (gramSquareBoolean a b c).det=
      (a*c-b^2)^2*((a^2+b^2)*(b^2+c^2)+(b*(a+c))^2) := by
  rw [gramSquareBoolean,det_booleanMatrix]
  ring

theorem gramSquareBoolean_positive_biased (a b c : ℝ)
    (hb : b≠0) (hd : a*c≠b^2) (hdiag : a^2≠c^2) :
    (∀i j,0<gramSquareBoolean a b c i j) ∧
    gramSquareBoolean a b c 0 0≠gramSquareBoolean a b c 1 1 ∧
    (gramSquareBoolean a b c).det≠0 := by
  have hb2 : 0<b^2 := sq_pos_of_ne_zero hb
  have ha2 : 0<a^2+b^2 := by nlinarith [sq_nonneg a]
  have hc2 : 0<b^2+c^2 := by nlinarith [sq_nonneg c]
  have hs : a+c≠0 := by
    intro h
    apply hdiag
    exact (sq_eq_sq_iff_eq_or_eq_neg).mpr (Or.inr (by linarith))
  refine ⟨?_,?_,?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact sq_pos_of_ne_zero ha2.ne'
    · exact sq_pos_of_ne_zero (mul_ne_zero hb hs)
    · exact sq_pos_of_ne_zero (mul_ne_zero hb hs)
    · exact sq_pos_of_ne_zero hc2.ne'
  · intro h
    change (a^2+b^2)^2=(b^2+c^2)^2 at h
    apply hdiag
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp h with h|h <;> nlinarith
  · rw [gramSquareBoolean_det]
    apply mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hd))
    apply ne_of_gt
    exact add_pos_of_pos_of_nonneg (mul_pos ha2 hc2) (sq_nonneg _)

theorem leafBoolean_det (a b c : ℝ) :
    (leafBoolean a b c).1*(leafBoolean a b c).2.2-(leafBoolean a b c).2.1^2=
      (a+b)^2*(b+c)^2*(a*c-b^2) := by
  simp only [leafBoolean]
  ring

theorem leafBoolean_opposite_diag_difference (a b : ℝ) :
    (leafBoolean a b (-a)).1^2-(leafBoolean a b (-a)).2.2^2=
      8*a^3*b*(a^2+b^2) := by
  simp only [leafBoolean]
  ring

/-- A single fixed endpoint-leaf gadget breaks the equal-magnitude diagonal
obstruction unless the matrix is in the literal signed Hadamard family. -/
theorem leafBoolean_opposite_good (a b : ℝ)
    (ha : a≠0) (hb : b≠0) (hab : a^2≠b^2) :
    (leafBoolean a b (-a)).2.1≠0 ∧
    (leafBoolean a b (-a)).1*(leafBoolean a b (-a)).2.2≠
      (leafBoolean a b (-a)).2.1^2 ∧
    (leafBoolean a b (-a)).1^2≠(leafBoolean a b (-a)).2.2^2 := by
  have hs : a+b≠0 := by intro h; apply hab; exact (sq_eq_sq_iff_eq_or_eq_neg).mpr (Or.inr (by linarith))
  have ht : b+-a≠0 := by intro h; apply hab; exact (sq_eq_sq_iff_eq_or_eq_neg).mpr (Or.inl (by linarith))
  have hd : a*(-a)-b^2≠0 := by
    have h : 0<a^2 := sq_pos_of_ne_zero ha
    nlinarith [sq_nonneg b]
  have hpos : 0<a^2+b^2 := by nlinarith [sq_pos_of_ne_zero ha,sq_nonneg b]
  refine ⟨mul_ne_zero (mul_ne_zero hb hs) ht,?_,?_⟩
  · apply sub_ne_zero.mp
    rw [leafBoolean_det]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ ht)) hd
  · apply sub_ne_zero.mp
    rw [leafBoolean_opposite_diag_difference]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) hb) hpos.ne'

/-- Every signed hard Boolean parameter is normalized by either no leaf or
one leaf at each terminal, followed by square/stretch. This is algebra only. -/
theorem signedBoolean_positive_target (a b c : ℝ) (h : ¬BooleanEasy a b c) :
    ∃x y z:ℝ, ((x=a ∧ y=b ∧ z=c) ∨ (x,y,z)=leafBoolean a b c) ∧
      (∀i j,0<gramSquareBoolean x y z i j) ∧
      gramSquareBoolean x y z 0 0≠gramSquareBoolean x y z 1 1 ∧
      (gramSquareBoolean x y z).det≠0 := by
  have hdet : a*c≠b^2 := fun hd=>h (Or.inl hd)
  have hb : b≠0 := fun hb=>h (Or.inr (Or.inl hb))
  have hac : a≠c := fun hac=>h (Or.inr (Or.inr (Or.inl hac)))
  by_cases hd : a^2=c^2
  · have hc : c=-a := by
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hd with he|he
      · exact False.elim (hac he)
      · linarith
    have ha : a≠0 := by intro ha; apply hac; rw [hc,ha,neg_zero]
    have hab : a^2≠b^2 := by
      intro he
      apply h
      apply Or.inr ∘ Or.inr ∘ Or.inr
      rw [hc]
      constructor <;> nlinarith
    obtain ⟨hy,hdet',hdiag⟩ := leafBoolean_opposite_good a b ha hb hab
    rw [←hc] at hy hdet' hdiag
    refine ⟨(leafBoolean a b c).1,(leafBoolean a b c).2.1,(leafBoolean a b c).2.2,
      Or.inr rfl,?_⟩
    exact gramSquareBoolean_positive_biased _ _ _ hy hdet' hdiag
  · exact ⟨a,b,c,Or.inl ⟨rfl,rfl,rfl⟩,gramSquareBoolean_positive_biased a b c hb hdet hd⟩

end PlanarHom.SignedThreeState
