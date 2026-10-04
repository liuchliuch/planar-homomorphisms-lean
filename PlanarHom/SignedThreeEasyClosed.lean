import PlanarHom.SignedThreeStateCriterion
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Ring.Basic

/-! NEW: the exact signed three-state easy set is closed in the whole real
matrix space. Arbitrary singleton signs and all Boolean exceptional equations
are retained. This supports exact rational-obstruction hardness. -/
noncomputable section
open Classical
namespace PlanarHom.SignedThreeState
variable {C : Type} [Fintype C]

theorem rank_le_one_iff_minors (M : Matrix C C ℝ) : M.rank ≤ 1 ↔
    ∀i j k l, M i k * M j l = M i l * M j k := by
  constructor
  · exact minor_eq_zero_of_rank_le_one M
  · intro h
    by_cases hz : M = 0
    · simp [hz]
    · have hn : ∃r c, M r c ≠ 0 := by
        by_contra h
        apply hz
        ext r c
        simpa using (not_exists.mp (not_exists.mp h r) c)
      obtain ⟨r,c,hrc⟩ := hn
      have he : M = Matrix.vecMulVec (fun i => M i c / M r c) (fun j => M r j) := by
        ext i j
        simp only [Matrix.vecMulVec_apply]
        rw [div_mul_eq_mul_div]
        exact (eq_div_iff hrc).mpr (h i r j c)
      rw [he]
      exact Matrix.rank_vecMulVec_le _ _

theorem isClosed_rank_le_one : IsClosed {M : Matrix C C ℝ | M.rank ≤ 1} := by
  simp only [rank_le_one_iff_minors,Set.setOf_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro l
  apply isClosed_eq <;> fun_prop

private def blockChart (p : Equiv.Perm (Fin 3)) (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  BooleanEasy (M (p.symm 0) (p.symm 0)) (M (p.symm 0) (p.symm 1)) (M (p.symm 1) (p.symm 1)) ∧
  ∀i j, M i j = blockMatrix (M (p.symm 0) (p.symm 0)) (M (p.symm 0) (p.symm 1))
    (M (p.symm 1) (p.symm 1)) (M (p.symm 2) (p.symm 2)) (p i) (p j)

private def starChart (p : Equiv.Perm (Fin 3)) (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀i j, M i j = starMatrix (M (p.symm 0) (p.symm 2)) (M (p.symm 1) (p.symm 2)) (p i) (p j)

private theorem easy_iff_charts (M : Matrix (Fin 3) (Fin 3) ℝ) : ThreeStateEasy M ↔
    M.rank ≤ 1 ∨ (∃p, blockChart p M) ∨ (∃p, starChart p M) := by
  constructor
  · rintro (hr | ⟨a,b,c,t,hb,p,hm⟩ | ⟨a,b,p,hm⟩)
    · exact Or.inl hr
    · have ha : M (p.symm 0) (p.symm 0) = a := by simpa [blockMatrix] using hm (p.symm 0) (p.symm 0)
      have hbb : M (p.symm 0) (p.symm 1) = b := by simpa [blockMatrix] using hm (p.symm 0) (p.symm 1)
      have hc : M (p.symm 1) (p.symm 1) = c := by simpa [blockMatrix] using hm (p.symm 1) (p.symm 1)
      have ht : M (p.symm 2) (p.symm 2) = t := by simpa [blockMatrix] using hm (p.symm 2) (p.symm 2)
      exact Or.inr (Or.inl ⟨p,by simpa only [blockChart,ha,hbb,hc,ht] using And.intro hb hm⟩)
    · have ha : M (p.symm 0) (p.symm 2) = a := by simpa [starMatrix] using hm (p.symm 0) (p.symm 2)
      have hb : M (p.symm 1) (p.symm 2) = b := by simpa [starMatrix] using hm (p.symm 1) (p.symm 2)
      exact Or.inr (Or.inr ⟨p,by simpa only [starChart,ha,hb] using hm⟩)
  · rintro (hr | ⟨p,hb,hm⟩ | ⟨p,hm⟩)
    · exact Or.inl hr
    · exact Or.inr (Or.inl ⟨_,_,_,_,hb,p,hm⟩)
    · exact Or.inr (Or.inr ⟨_,_,p,hm⟩)

private theorem continuous_block (i j : Fin 3) (a b c t : Matrix (Fin 3) (Fin 3) ℝ → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (ht : Continuous t) :
    Continuous (fun M => blockMatrix (a M) (b M) (c M) (t M) i j) := by
  fin_cases i <;> fin_cases j <;> simp [blockMatrix] <;> fun_prop

private theorem continuous_star (i j : Fin 3) (a b : Matrix (Fin 3) (Fin 3) ℝ → ℝ)
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun M => starMatrix (a M) (b M) i j) := by
  fin_cases i <;> fin_cases j <;> simp [starMatrix] <;> fun_prop

private theorem isClosed_blockChart (p : Equiv.Perm (Fin 3)) : IsClosed {M | blockChart p M} := by
  unfold blockChart BooleanEasy
  simp only [Set.setOf_and,Set.setOf_or,Set.setOf_forall]
  apply IsClosed.inter
  · apply IsClosed.union
    · apply isClosed_eq <;> fun_prop
    · apply IsClosed.union
      · apply isClosed_eq <;> fun_prop
      · apply IsClosed.union
        · apply isClosed_eq <;> fun_prop
        · apply IsClosed.inter <;> (apply isClosed_eq <;> fun_prop)
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_eq
    · fun_prop
    · exact continuous_block _ _ _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

private theorem isClosed_starChart (p : Equiv.Perm (Fin 3)) : IsClosed {M | starChart p M} := by
  simp only [starChart,Set.setOf_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_eq
  · fun_prop
  · exact continuous_star _ _ _ _ (by fun_prop) (by fun_prop)

theorem isClosed_threeStateEasy : IsClosed {M : Matrix (Fin 3) (Fin 3) ℝ | ThreeStateEasy M} := by
  simp only [easy_iff_charts,Set.setOf_or,Set.setOf_exists]
  exact isClosed_rank_le_one.union ((isClosed_iUnion_of_finite (fun p => isClosed_blockChart p)).union
    (isClosed_iUnion_of_finite (fun p => isClosed_starChart p)))

end PlanarHom.SignedThreeState
