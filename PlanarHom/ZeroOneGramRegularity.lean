import PlanarHom.ZeroOneGramComponentGeometry

/-! NEW §7 regularity argument. Equal-rank partner Gram blocks force equal
block sizes. Double-counting the original zero-one incidences then makes the
original degree constant across every edge, including loops. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.ZeroOneGramRegularity
open RootedRestriction StrictTensorSupportBlocks ZeroOneGramBlockClassification
open ZeroOneGramComponentGeometry
variable {q : ℕ}
variable (A : Matrix (Fin q) (Fin q) ℝ) (hs : ∀i j,A i j=A j i)
variable (h01 : ∀i j,A i j=0 ∨ A i j=1)

abbrev degree (i : Fin q) : ℝ := ∑j,A i j

include h01

theorem nonnegative : ∀i j,0≤A i j := by
  intro i j
  rcases h01 i j with h|h <;> rw [h] <;> norm_num

include hs in
theorem square_diagonal (i : Fin q) : (A*A) i i=degree A i := by
  simp only [Matrix.mul_apply,degree]
  apply Finset.sum_congr rfl
  intro j _
  rw [hs j i]
  rcases h01 i j with h|h <;> rw [h] <;> norm_num

theorem degree_constant (hb : Blocks (graph A hs) (A*A))
    (c : (graph A hs).ConnectedComponent) (i j : c.supp) : degree A i.val=degree A j.val := by
  rw [←square_diagonal A hs h01 i.val,←square_diagonal A hs h01 j.val]
  exact (hb c).diagonal_constant i j

theorem degree_edge (hb : Blocks (graph A hs) (A*A))
    (i j : Fin q) (hij : A i j≠0) : degree A i=degree A j := by
  let c := (graph A hs).connectedComponentMk i
  let d := (graph A hs).connectedComponentMk j
  let x : c.supp := ⟨i,rfl⟩
  let y : d.supp := ⟨j,rfl⟩
  have hnn := nonnegative A h01
  have hji : A j i≠0 := by simpa only [hs j i] using hij
  have hc (u : c.supp) (z : Fin q) (hn : A u.val z≠0) : z∈d.supp :=
    partner_closed A hs hnn hb c x j hij u z hn
  have hd (v : d.supp) (z : Fin q) (hn : A v.val z≠0) : z∈c.supp :=
    partner_closed A hs hnn hb d y i hji v z hn
  have hsumc (u : c.supp) : (∑v : d.supp,A u.val v.val)=degree A i := by
    rw [sum_on_support d.supp (fun z=>A u.val z) (fun z hz=>by
      by_contra he
      exact hz (hc u z he))]
    exact degree_constant A hs h01 hb c u x
  have hsumd (v : d.supp) : (∑u : c.supp,A u.val v.val)=degree A j := by
    simp_rw [hs _ v.val]
    rw [sum_on_support c.supp (fun z=>A v.val z) (fun z hz=>by
      by_contra he
      exact hz (hd v z he))]
    exact degree_constant A hs h01 hb d v y
  have hcounts : (Fintype.card c.supp : ℝ)*degree A i=(Fintype.card d.supp : ℝ)*degree A j := by
    calc
      _ = ∑u : c.supp,∑v : d.supp,A u.val v.val := by simp only [hsumc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ = ∑v : d.supp,∑u : c.supp,A u.val v.val := Finset.sum_comm
      _ = _ := by simp only [hsumd,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcard := partner_card A hs hnn hb c x j hij
  have hn : (Fintype.card c.supp : ℝ)≠0 := by
    letI : Nonempty c.supp := ⟨x⟩
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty c.supp)).ne'
  rw [←hcard] at hcounts
  exact mul_left_cancel₀ hn hcounts

theorem square_row_sum (hb : Blocks (graph A hs) (A*A)) (i : Fin q) :
    (∑j,(A*A) i j)=(degree A i)^2 := by
  calc
    (∑j,(A*A) i j) = ∑k,A i k*degree A k := by
      simp only [Matrix.mul_apply,degree,Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑k,A i k*degree A i := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hik : A i k=0
      · simp [hik]
      · rw [degree_edge A hs h01 hb i k hik]
    _ = (degree A i)^2 := by rw [←Finset.sum_mul]; simp only [degree,pow_two]

theorem square_block_row_sum (hb : Blocks (graph A hs) (A*A))
    (c : (graph A hs).ConnectedComponent) (i : c.supp) :
    (∑j : c.supp,(A*A) i.val j.val)=(degree A i.val)^2 := by
  rw [sum_on_support c.supp (fun j=>(A*A) i.val j) (fun j hj=>by
    by_contra hn
    exact hj (component_colorClosed (A*A) (square_symmetric A hs) c i.val i.property j hn))]
  exact square_row_sum A hs h01 hb i.val

end PlanarHom.ZeroOneGramRegularity
