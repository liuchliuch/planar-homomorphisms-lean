import PlanarHom.FixedRealActualTwins

/-! NEW literal numerical quotient transport through a prescribed embedding. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealActualTwins
variable {K C : Type} [Field K] [Fintype C]

def rowEquivTo (φ : K →+* ℝ) (A : Matrix C C K) (B : Matrix C C ℝ)
    (hB : ∀ i j, φ (A i j) = B i j) :
    Quotient (Twins.rowSetoid A) ≃ Quotient (Twins.rowSetoid B) where
  toFun := Quotient.map id (by intro i j h k; change B i k=B j k; rw [←hB i k,←hB j k]; exact congrArg φ (h k))
  invFun := Quotient.map id (by intro i j h k; apply φ.injective; change φ (A i k)=φ (A j k); rw [hB i k,hB j k]; exact h k)
  left_inv x := Quotient.inductionOn x (fun _ => rfl)
  right_inv x := Quotient.inductionOn x (fun _ => rfl)

@[simp] theorem rowEquivTo_mk (φ : K →+* ℝ) (A : Matrix C C K) (B : Matrix C C ℝ)
    (hB : ∀ i j, φ (A i j) = B i j) (i : C) :
    rowEquivTo φ A B hB (Quotient.mk _ i) = Quotient.mk _ i := rfl

theorem quotientMatrix_map_to (φ : K →+* ℝ) (A : Matrix C C K) (hs : ∀ i j,A i j=A j i)
    (B : Matrix C C ℝ) (hsB : ∀ i j,B i j=B j i) (hB : ∀ i j,φ (A i j)=B i j)
    (x y : Quotient (Twins.rowSetoid A)) :
    φ (Twins.quotientMatrix A hs x y) = Twins.quotientMatrix B hsB
      (rowEquivTo φ A B hB x) (rowEquivTo φ A B hB y) := by
  induction x using Quotient.inductionOn with
  | h i => induction y using Quotient.inductionOn with
    | h j => exact hB i j

theorem quotientWeight_map_to (φ : K →+* ℝ) (A : Matrix C C K) (B : Matrix C C ℝ)
    (hB : ∀ i j,φ (A i j)=B i j) (w : C → K) (x : Quotient (Twins.rowSetoid A)) :
    φ (Twins.quotientWeight A w x) =
      Twins.quotientWeight B (fun i => φ (w i)) (rowEquivTo φ A B hB x) := by
  have hp : ∀ i, (Quotient.mk (Twins.rowSetoid A) i=x) ↔
      (Quotient.mk (Twins.rowSetoid B) i=rowEquivTo φ A B hB x) := by
    intro i
    exact ⟨fun h => congrArg (rowEquivTo φ A B hB) h,fun h => (rowEquivTo φ A B hB).injective h⟩
  unfold Twins.quotientWeight
  rw [map_sum]
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight hp) _ _ (fun _ => rfl)

theorem quotientWeight_map_pos (φ : K →+* ℝ) (A : Matrix C C K) (w : C → K)
    (hw : ∀ i,0<φ (w i)) (x : Quotient (Twins.rowSetoid A)) :
    0<φ (Twins.quotientWeight A w x) := by
  letI : Nonempty {i // Quotient.mk (Twins.rowSetoid A) i=x} := ⟨⟨x.out,Quotient.out_eq x⟩⟩
  unfold Twins.quotientWeight
  rw [map_sum]
  exact Finset.sum_pos (fun i _ => hw i.val) Finset.univ_nonempty

end PlanarHom.FixedRealActualTwins
