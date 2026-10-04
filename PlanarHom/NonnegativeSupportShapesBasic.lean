-- Exact recovered pure shape construction, separated from numerical support hardness.
import PlanarHom.ZeroOneBasicStructure
import Mathlib.Logic.Equiv.Sum

/-! The literal matrix shapes forced by basic numerical support. The positive
cross block and both finite color charts are constructed from actual fibers;
no square or equal-size bipartition is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.NonnegativeSupportShapes
open ZeroOneBasicStructure
variable {C : Type} [Fintype C]

def double {p r : ℕ} (V : Matrix (Fin p) (Fin r) ℝ) :
    Matrix (Fin p⊕Fin r) (Fin p⊕Fin r) ℝ :=
  fun i j=>Sum.elim (fun a=>Sum.elim (fun _=>0) (fun b=>V a b) j)
    (fun b=>Sum.elim (fun a=>V a b) (fun _=>0) j) i

inductive Shape (M : Matrix C C ℝ) : Prop
  | positive (h : ∀ i j,0<M i j)
  | bipartite (p r : ℕ) (hp : 0<p) (hr : 0<r) (e : C≃Fin p⊕Fin r)
      (V : Matrix (Fin p) (Fin r) ℝ) (hV : ∀ i j,0<V i j)
      (hM : Matrix.reindex e e M=double V)
  | zero (e : C≃Unit) (hM : M=0)

theorem support_zero_iff (x : ℝ) : (if x=0 then (0:ℝ) else 1)=0 ↔ x=0 := by
  by_cases h:x=0 <;> simp [h]

theorem shape_of_basic_support (M : Matrix C C ℝ)
    (hs : ∀ i j,M i j=M j i) (hnn : ∀ i j,0≤M i j)
    (hb : BasicZeroOneComponent (fun i j=>if M i j=0 then (0:ℝ) else 1)) : Shape M := by
  rcases hb with ⟨hne,hones⟩|⟨s,hsurj,hb⟩|⟨hne,hsub,hzero⟩
  · apply Shape.positive
    intro i j
    have hz : M i j≠0 := by
      intro h
      have ho := hones i j
      simp [h] at ho
    exact lt_of_le_of_ne (hnn i j) hz.symm
  · change ∀ i j,(if M i j=0 then (0:ℝ) else 1)=(if s i=s j then 0 else 1) at hb
    let P : C→Prop := fun i=>s i=false
    let X := {i // P i}
    let Y := {i // ¬P i}
    have hX : Nonempty X := by obtain ⟨i,hi⟩:=hsurj false; exact ⟨⟨i,hi⟩⟩
    have hY : Nonempty Y := by obtain ⟨i,hi⟩:=hsurj true; exact ⟨⟨i,by simp [P,hi]⟩⟩
    letI := hX
    letI := hY
    let p := Fintype.card X
    let r := Fintype.card Y
    let f : Fin p⊕Fin r≃C :=
      (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin Y).symm).trans (Equiv.sumCompl P)
    have hfL (i : Fin p) : s (f (.inl i))=false := ((Fintype.equivFin X).symm i).property
    have hfR (j : Fin r) : s (f (.inr j))=true := by
      have hh : s (f (.inr j))≠false := ((Fintype.equivFin Y).symm j).property
      cases he:s (f (.inr j)) <;> simp_all
    have hzero (i j : C) : M i j=0 ↔ s i=s j := by
      rw [←support_zero_iff,hb]
      by_cases h:s i=s j <;> simp [h]
    let V : Matrix (Fin p) (Fin r) ℝ := fun i j=>M (f (.inl i)) (f (.inr j))
    have hV : ∀ i j,0<V i j := by
      intro i j
      apply lt_of_le_of_ne (hnn _ _)
      intro hh
      have ht := (hzero _ _).mp hh.symm
      rw [hfL,hfR] at ht
      exact Bool.false_ne_true ht
    refine Shape.bipartite p r Fintype.card_pos Fintype.card_pos f.symm V hV ?_
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact (hzero _ _).mpr ((hfL i).trans (hfL j).symm)
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j => exact hs _ _
      | inr j => exact (hzero _ _).mpr ((hfR i).trans (hfR j).symm)
  · let e : C≃Unit := {
      toFun:=fun _=>()
      invFun:=fun _=>Classical.choice hne
      left_inv:=fun i=>hsub.allEq _ _
      right_inv:=fun u=>by cases u; rfl }
    refine Shape.zero e ?_
    funext i j
    apply (support_zero_iff _).mp
    exact congrFun (congrFun hzero i) j

end PlanarHom.NonnegativeSupportShapes
