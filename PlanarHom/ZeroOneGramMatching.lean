import PlanarHom.ZeroOneGramRegularity
import PlanarHom.IntegerIsingTensorObstruction

/-! NEW §7 integer obstruction on the actual square-support blocks. Their
row sum is the square of the original degree. Integrality excludes every
nonzero Boolean tensor dimension, forcing the original twin-free matrix to
be a disjoint union of loops and single edges. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.ZeroOneGramMatching
open RootedRestriction StrictTensorSupportBlocks ZeroOneGramBlockClassification
open ZeroOneGramComponentGeometry ZeroOneGramRegularity Boolean
variable {q : ℕ}
variable (A : Matrix (Fin q) (Fin q) ℝ) (hs : ∀i j,A i j=A j i)
variable (h01 : ∀i j,A i j=0 ∨ A i j=1)

include h01 in
theorem entry_natural (i j : Fin q) : ∃n:ℕ,A i j=(n:ℝ) := by
  rcases h01 i j with h|h
  · exact ⟨0,by simpa only [Nat.cast_zero] using h⟩
  · exact ⟨1,by simpa only [Nat.cast_one] using h⟩

theorem sum_natural {I : Type} [Fintype I] (f : I→ℝ) (hf : ∀i,∃n:ℕ,f i=(n:ℝ)) :
    ∃n:ℕ,(∑i,f i)=(n:ℝ) := by
  choose n hn using hf
  refine ⟨∑i,n i,?_⟩
  simp only [Nat.cast_sum,hn]

include h01 in
theorem square_natural (i j : Fin q) : ∃n:ℕ,(A*A) i j=(n:ℝ) := by
  change ∃n:ℕ,(∑z,A i z*A z j)=(n:ℝ)
  apply sum_natural
  intro z
  obtain ⟨a,ha⟩ := entry_natural A h01 i z
  obtain ⟨b,hb⟩ := entry_natural A h01 z j
  exact ⟨a*b,by rw [ha,hb,Nat.cast_mul]⟩

include h01 in
theorem block_subsingleton (hb : Blocks (graph A hs) (A*A))
    (c : (graph A hs).ConnectedComponent) : Subsingleton c.supp := by
  obtain ⟨d,e,γ,ρ,hγ,hρ,hm⟩ := hb c
  let i := e.symm (fun _=>false)
  obtain ⟨n,hn⟩ := square_natural A h01 i.val i.val
  have hγn : γ=(n:ℝ) := by
    have he := hm i i
    simp only [tensor_diag,mul_one] at he
    exact he.symm.trans hn
  have hnpos : 0<n := by exact_mod_cast (hγn ▸ hγ)
  have hdeg : degree A i.val=(n:ℝ) := (square_diagonal A hs h01 i.val).symm.trans hn
  have hrow : (n:ℝ)=∏r,(1+ρ r) := by
    have hr := square_block_row_sum A hs h01 hb c i
    have he : (∑j : c.supp,(A*A) i.val j.val)=γ*∏r,(1+ρ r) := by
      calc
        _ = ∑y : Cube d,γ*tensor ρ (fun _=>false) y := by
          apply Fintype.sum_equiv e
          intro j
          simpa only [i,e.apply_symm_apply] using hm i j
        _ = _ := by rw [←Finset.mul_sum,tensor_row_sum]
    rw [he,hγn,hdeg,pow_two] at hr
    exact (mul_left_cancel₀ (ne_of_gt (by exact_mod_cast hnpos : 0<(n:ℝ))) hr).symm
  have hd : d=0 := by
    by_contra hd
    apply IntegerIsingTensorObstruction.impossible (Nat.pos_of_ne_zero hd) n hnpos ρ hρ _ hrow
    intro x
    obtain ⟨m,hmNat⟩ := square_natural A h01 i.val (e.symm x).val
    refine ⟨m,?_⟩
    have he := hm i (e.symm x)
    simp only [i,e.apply_symm_apply,hγn] at he
    exact he.symm.trans hmNat
  subst d
  refine ⟨fun x y=>e.injective ?_⟩
  exact Subsingleton.elim _ _

include h01 in
theorem neighbors_unique (hb : Blocks (graph A hs) (A*A))
    (i j k : Fin q) (hij : A i j≠0) (hik : A i k≠0) : j=k := by
  let c := (graph A hs).connectedComponentMk j
  have hj : j∈c.supp := rfl
  have hk : k∈c.supp := (neighbors_same_component A hs (nonnegative A h01) i j k hij hik).symm
  have he := (block_subsingleton A hs h01 hb c).allEq (⟨j,hj⟩ : c.supp) ⟨k,hk⟩
  exact congrArg Subtype.val he

end PlanarHom.ZeroOneGramMatching
