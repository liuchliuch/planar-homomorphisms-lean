import PlanarHom.RankFourSplitNecessity
import PlanarHom.RankFourBooleanTensorClosure

/-! Exact four-state structural specialization: a nonempty 1+3 or 2+2
simultaneous direct sum of tractable blocks, or a tensor of two nonnegative
Boolean matrices satisfying the original Boolean equations. -/
noncomputable section
open Classical
namespace PlanarHom.RankFour
open Structures

/-- The subset split is equivalent to this ordinary numbered direct-sum chart. -/
def DirectSumClass (M:Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃(n m:ℕ)(A:Matrix (Fin n) (Fin n) ℝ)(B:Matrix (Fin m) (Fin m) ℝ)
    (e:Fin 4≃Fin n⊕Fin m),
    ((n=1 ∧ m=3) ∨ (n=2 ∧ m=2)) ∧ NonnegativeClass A ∧ NonnegativeClass B ∧
    ∀i j,M (e.symm i) (e.symm j)=sumMatrix A B i j

theorem SplitClass.directSumClass {M:Matrix (Fin 4) (Fin 4) ℝ} (h:SplitClass M) :
    DirectSumClass M := by
  obtain ⟨p,hsize,hz,hz',ha,hb⟩:=h
  let ea:=Fintype.equivFin {i//p i}
  let eb:=Fintype.equivFin {i//¬p i}
  let A:Matrix _ _ ℝ:=fun i j=>M (ea.symm i).val (ea.symm j).val
  let B:Matrix _ _ ℝ:=fun i j=>M (eb.symm i).val (eb.symm j).val
  let e:Fin 4≃_ := (Equiv.sumCompl p).symm.trans (Equiv.sumCongr ea eb)
  refine ⟨_,_,A,B,e,?_,ha.equiv ea.symm,hb.equiv eb.symm,?_⟩
  · simpa only [Nat.card_eq_fintype_card] using hsize
  · intro i j
    cases i with
    | inl i=>cases j with
      | inl j=>rfl
      | inr j=>exact hz _ _ (ea.symm i).property (eb.symm j).property
    | inr i=>cases j with
      | inl j=>exact hz' _ _ (eb.symm i).property (ea.symm j).property
      | inr j=>rfl

theorem DirectSumClass.nonnegativeClass {M:Matrix (Fin 4) (Fin 4) ℝ} (h:DirectSumClass M) :
    NonnegativeClass M := by
  obtain ⟨n,m,A,B,e,hs,ha,hb,hm⟩:=h
  have h:=(ha.sum hb).equiv e
  convert h using 1
  funext i j
  simpa only [Equiv.symm_apply_apply] using hm (e i) (e j)

def FourStateClass (M:Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  DirectSumClass M ∨ BooleanTensorClass M

theorem nonnegativeClass_iff_fourStateClass {M:Matrix (Fin 4) (Fin 4) ℝ}
    (hr:M.rank=4) : NonnegativeClass M ↔ FourStateClass M := by
  constructor
  · intro h
    rcases nonnegativeClass_rank_four_forms hr h with h|h
    · exact .inl h.directSumClass
    · exact .inr h.booleanTensorClass
  · intro h
    rcases h with h|h
    · exact h.nonnegativeClass
    · exact h.nonnegativeClass (by simpa only [Fintype.card_fin] using hr)

end PlanarHom.RankFour
