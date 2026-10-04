import PlanarHom.ActualTwinRowFacts
import PlanarHom.AlgebraicLanguagePresentation
import PlanarHom.ActualTwinReduction

/-! Canonical real-language presentation of an actual numerical row quotient,
with a charged field-descent/reindexing reduction to its original field basis. -/
noncomputable section
open Classical
namespace PlanarHom.FiniteFieldQuotientLanguage
open Complexity Complexity.MixedCode AlgebraicProductInterpolation
variable {C : Type} [Fintype C] {F : IntermediateField ℚ ℝ} {d : ℕ}

def index (A : Matrix C C F) : Fin (Fintype.card (Quotient (Twins.rowSetoid A))) ≃
    Quotient (Twins.rowSetoid A) := (Fintype.equivFin _).symm

def matrix (A : Matrix C C F) (hs : ∀ i j,A i j=A j i) :=
  fun i j => Twins.quotientMatrix A hs (index A i) (index A j)

def weight (A : Matrix C C F) (w : C → F) :=
  fun i => Twins.quotientWeight A w (index A i)

def language (basis : Module.Basis (Fin d) ℚ F) (A : Matrix C C F)
    (hs : ∀ i j,A i j=A j i) (w : C → F) :
    RealLanguage (Fintype.card (Quotient (Twins.rowSetoid A))) 1 0 := by
  letI : FiniteDimensional ℚ F := FiniteDimensional.of_fintype_basis basis
  exact {
    matrices := fun _ i j => (matrix A hs i j:ℝ)
    unaries := fun l => l.elim0
    weights := fun i => (weight A w i:ℝ)
    matrices_algebraic := fun _ i j => (IsAlgebraic.of_finite ℚ (matrix A hs i j)).algHom F.val
    unaries_algebraic := fun l => l.elim0
    weights_algebraic := fun i => (IsAlgebraic.of_finite ℚ (weight A w i)).algHom F.val }

def reduction (basis : Module.Basis (Fin d) ℚ F) (A : Matrix C C F)
    (hs : ∀ i j,A i j=A j i) (w : C → F) :
    PromisePolyTimeTuringReduction (language basis A hs w).problem
      (evaluationProblem basis (fun _ : Fin 1 => Twins.quotientMatrix A hs)
        (fun l : Fin 0 => l.elim0) (Twins.quotientWeight A w)) :=
  ((language basis A hs w).presentationDescentReduction F basis
    (fun _ => matrix A hs) (fun l : Fin 0 => l.elim0) (weight A w)
    (fun _ _ _ => rfl) (fun l => l.elim0) (fun _ => rfl)).trans
    (ActualTwins.reindexReduction basis (Twins.quotientMatrix A hs) (Twins.quotientWeight A w) (index A))

theorem matrix_symmetric (A : Matrix C C F) (hs : ∀ i j,A i j=A j i) :
    ∀ i j,matrix A hs i j=matrix A hs j i :=
  fun i j => Twins.quotientMatrix_symmetric A hs _ _

theorem matrix_rows_injective (A : Matrix C C F) (hs : ∀ i j,A i j=A j i) :
    Function.Injective (matrix A hs) := by
  intro i j h
  apply (index A).injective
  apply Twins.quotientMatrix_rows_injective A hs
  funext x
  have hx := congrFun h ((index A).symm x)
  simpa only [matrix,Equiv.apply_symm_apply] using hx

theorem real_matrix_rows_injective (A : Matrix C C F) (hs : ∀ i j,A i j=A j i) :
    Function.Injective (fun i j => (matrix A hs i j:ℝ)) := by
  intro i j h
  apply matrix_rows_injective A hs
  funext k
  exact Subtype.ext (congrFun h k)

/-- The computational field quotient and the literal original real quotient
identify exactly the same original colors. The target real matrix is fixed. -/
def realQuotientEquiv (A : Matrix C C F) (B : Matrix C C ℝ)
    (hB : ∀ i j,(A i j:ℝ)=B i j) :
    Quotient (Twins.rowSetoid A) ≃ Quotient (Twins.rowSetoid B) where
  toFun := Quotient.map id (by
    intro i j h k
    change B i k=B j k
    rw [←hB i k,←hB j k]
    exact congrArg (fun z : F => (z:ℝ)) (h k))
  invFun := Quotient.map id (by
    intro i j h k
    apply Subtype.ext
    change (A i k:ℝ)=(A j k:ℝ)
    rw [hB i k,hB j k]
    exact h k)
  left_inv x := Quotient.inductionOn x (fun _ => rfl)
  right_inv x := Quotient.inductionOn x (fun _ => rfl)

@[simp] theorem realQuotientEquiv_mk (A : Matrix C C F) (B : Matrix C C ℝ)
    (hB : ∀ i j,(A i j:ℝ)=B i j) (i : C) :
    realQuotientEquiv A B hB (Quotient.mk _ i)=Quotient.mk _ i := rfl

theorem quotientMatrix_real (A : Matrix C C F) (hsA : ∀ i j,A i j=A j i)
    (B : Matrix C C ℝ) (hsB : ∀ i j,B i j=B j i)
    (hB : ∀ i j,(A i j:ℝ)=B i j) (x y : Quotient (Twins.rowSetoid A)) :
    (Twins.quotientMatrix A hsA x y:ℝ)=Twins.quotientMatrix B hsB
      (realQuotientEquiv A B hB x) (realQuotientEquiv A B hB y) := by
  induction x using Quotient.inductionOn with
  | h i =>
    induction y using Quotient.inductionOn with
    | h j => exact hB i j

theorem quotientWeight_real (A : Matrix C C F) (B : Matrix C C ℝ)
    (hB : ∀ i j,(A i j:ℝ)=B i j) (w : C → F) (x : Quotient (Twins.rowSetoid A)) :
    ((Twins.quotientWeight A w x:F):ℝ)=Twins.quotientWeight B (fun i : C => (w i:ℝ))
      (realQuotientEquiv A B hB x) := by
  let e := realQuotientEquiv A B hB
  have hp : ∀ i,(Quotient.mk (Twins.rowSetoid A) i=x) ↔
      (Quotient.mk (Twins.rowSetoid B) i=e x) := by
    intro i
    constructor
    · intro h
      simpa only [e,realQuotientEquiv_mk] using congrArg e h
    · intro h
      apply e.injective
      exact h
  let ef := Equiv.subtypeEquivRight hp
  unfold Twins.quotientWeight
  change F.val.toRingHom (∑ i : {c // Quotient.mk (Twins.rowSetoid A) c=x},w i.val)=_
  rw [map_sum]
  exact Fintype.sum_equiv ef _ _ (fun _ => rfl)

theorem matrix_entry (A : Matrix C C F) (hs : ∀ i j,A i j=A j i) (i j) :
    matrix A hs i j=A (index A i).out (index A j).out := by
  have h := Twins.quotientMatrix_mk A hs (index A i).out (index A j).out
  rw [Quotient.out_eq,Quotient.out_eq] at h
  exact h

theorem real_matrix_pos (A : Matrix C C F) (hs : ∀ i j,A i j=A j i)
    (hpos : ∀ i j,0<(A i j:ℝ)) : ∀ i j,0<(matrix A hs i j:ℝ) := by
  intro i j
  rw [matrix_entry]
  exact hpos _ _

theorem real_matrix_diag (A : Matrix C C F) (hs : ∀ i j,A i j=A j i)
    (hdiag : ∀ i,(A i i:ℝ)=1) : ∀ i,(matrix A hs i i:ℝ)=1 := by
  intro i
  rw [matrix_entry]
  exact hdiag _

end PlanarHom.FiniteFieldQuotientLanguage
