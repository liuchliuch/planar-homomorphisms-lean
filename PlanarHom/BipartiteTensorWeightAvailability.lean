import PlanarHom.BipartiteTensorWeightUnary
import PlanarHom.PositiveRealBipartiteDouble

/-! Actual canonical algebraic source reductions to both decorated same-side
Gram matrices. The support is literally a closed side of the squared double;
there is no assumed arbitrary component or free side-pinning oracle. -/
noncomputable section
open Classical
namespace PlanarHom.BipartiteTensorWeight
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity PositiveRealCore RootedRestriction
variable {I : Type} [Fintype I] [DecidableEq I] {q : ℕ}

variable (e : Fin q ≃ I ⊕ I)

def leftSupport : Set (Fin q) := Set.range (fun i : I=>e.symm (.inl i))
def rightSupport : Set (Fin q) := Set.range (fun i : I=>e.symm (.inr i))

def leftIndex : I ≃ leftSupport e :=
  Equiv.ofInjective (fun i : I=>e.symm (.inl i)) (e.symm.injective.comp Sum.inl_injective)
def rightIndex : I ≃ rightSupport e :=
  Equiv.ofInjective (fun i : I=>e.symm (.inr i)) (e.symm.injective.comp Sum.inr_injective)

def leftCoordinate : Fin (Fintype.card (leftSupport e)) ≃ I :=
  (Fintype.equivFin (leftSupport e)).symm.trans (leftIndex e).symm
def rightCoordinate : Fin (Fintype.card (rightSupport e)) ≃ I :=
  (Fintype.equivFin (rightSupport e)).symm.trans (rightIndex e).symm

theorem leftCoordinate_value (i : Fin (Fintype.card (leftSupport e))) :
    e ((Fintype.equivFin (leftSupport e)).symm i).val = .inl (leftCoordinate e i) := by
  have h := congrArg (fun x : leftSupport e=>e x.val)
    ((leftIndex e).apply_symm_apply ((Fintype.equivFin (leftSupport e)).symm i))
  change e (e.symm (.inl (leftCoordinate e i))) = _ at h
  simpa only [Equiv.apply_symm_apply] using h.symm

theorem rightCoordinate_value (i : Fin (Fintype.card (rightSupport e))) :
    e ((Fintype.equivFin (rightSupport e)).symm i).val = .inr (rightCoordinate e i) := by
  have h := congrArg (fun x : rightSupport e=>e x.val)
    ((rightIndex e).apply_symm_apply ((Fintype.equivFin (rightSupport e)).symm i))
  change e (e.symm (.inr (rightCoordinate e i))) = _ at h
  simpa only [Equiv.apply_symm_apply] using h.symm

variable (L : RealLanguage q 1 0) (B : Matrix I I ℝ) (μ ν : I→ℝ)
variable (hM : ∀ i j,L.matrices 0 i j=doubleMatrix B (e i) (e j))
variable (hw : ∀ i,L.weights i=Sum.elim μ ν (e i))
variable (hμ : ∀ i,0<μ i) (hν : ∀ i,0<ν i)

include hw hμ hν in
theorem source_weights_positive : ∀ i,0<L.weights i := by
  intro i
  rw [hw]
  cases e i with
  | inl x => exact hμ x
  | inr x => exact hν x

include hM in
theorem source_symmetric : ∀ i j,L.matrices 0 i j=L.matrices 0 j i := by
  intro i j
  rw [hM,hM]
  exact congrArg (fun A=>A (e j) (e i)) (doubleMatrix_transpose B)

include hM in
theorem source_rows_nonzero (hB : IsUnit B) : ∀ i,L.matrices 0 i≠0 := by
  intro i hz
  apply doubleMatrix_rows_nonzero B hB (e i)
  funext j
  have h := congrFun hz (e.symm j)
  simpa only [hM,Equiv.apply_symm_apply,Pi.zero_apply] using h

include hM in
theorem source_rows_nonproportional (hB : IsUnit B) :
    ∀ i j,i≠j→∀ t:ℝ,L.matrices 0 i≠t • L.matrices 0 j := by
  intro i j hij t he
  apply doubleMatrix_rows_nonproportional B hB (e.injective.ne hij) t
  funext k
  have h := congrFun he (e.symm k)
  simpa only [hM,Equiv.apply_symm_apply,Pi.smul_apply] using h

local notation "hp" => source_weights_positive e L μ ν hw hμ hν

include hM hw in
theorem decorated_source_matrix :
    decoratedMatrix L 0=(doubleMatrix (decorated B μ ν)).submatrix e e := by
  ext i j
  change Real.sqrt (L.weights i)*L.matrices 0 i j*Real.sqrt (L.weights j)=_
  rw [hM,hw,hw]
  rw [←decorated_doubleMatrix]
  exact (decorated_entry _ _ _ (e i) (e j)).symm

include hM in
theorem squared_source_matrix :
    (squareLanguage L 0 hp).matrices 0=
      (Matrix.fromBlocks (leftGram B μ ν) 0 0 (rightGram B μ ν)).submatrix e e := by
  rw [squareLanguage_matrix,decorated_source_matrix e L B μ ν hM hw,
    Matrix.submatrix_mul_equiv _ _ e e e,doubleMatrix_square]
  rfl

include hM in
theorem square_source_symmetric :
    ∀ i j,(squareLanguage L 0 hp).matrices 0 i j=(squareLanguage L 0 hp).matrices 0 j i := by
  let D := decoratedMatrix L 0
  have hs : D.transpose=D := by
    rw [show D=decoratedMatrix L 0 from rfl,decorated_source_matrix e L B μ ν hM hw]
    rw [Matrix.transpose_submatrix,doubleMatrix_transpose]
  intro i j
  have hsq : (D*D).transpose=D*D := by rw [Matrix.transpose_mul,hs]
  rw [squareLanguage_matrix]
  exact congrArg (fun A=>A j i) hsq

include hM in
theorem square_left_closed : ColorClosed ((squareLanguage L 0 hp).matrices 0) (leftSupport e) := by
  intro i hi j hij
  obtain ⟨x,rfl⟩ := hi
  cases hj : e j with
  | inl y => exact ⟨y,(e.symm_apply_apply j).symm.trans (congrArg e.symm hj) |>.symm⟩
  | inr y =>
    apply False.elim
    apply hij
    rw [squared_source_matrix e L B μ ν hM hw hμ hν]
    simp [Matrix.submatrix_apply,hj]

include hM in
theorem square_right_closed : ColorClosed ((squareLanguage L 0 hp).matrices 0) (rightSupport e) := by
  intro i hi j hij
  obtain ⟨x,rfl⟩ := hi
  cases hj : e j with
  | inr y => exact ⟨y,(e.symm_apply_apply j).symm.trans (congrArg e.symm hj) |>.symm⟩
  | inl y =>
    apply False.elim
    apply hij
    rw [squared_source_matrix e L B μ ν hM hw hμ hν]
    simp [Matrix.submatrix_apply,hj]

def leftLanguage := (squareLanguage L 0 hp).supportFiniteLanguage (leftSupport e)
def rightLanguage := (squareLanguage L 0 hp).supportFiniteLanguage (rightSupport e)

include hM in
theorem leftLanguage_matrix (i j : Fin (Fintype.card (leftSupport e))) :
    (leftLanguage e L μ ν hw hμ hν).matrices 0 i j=
      leftGram B μ ν (leftCoordinate e i) (leftCoordinate e j) := by
  change (squareLanguage L 0 hp).matrices 0 _ _=_
  rw [squared_source_matrix e L B μ ν hM hw hμ hν]
  simp only [Matrix.submatrix_apply,leftCoordinate_value,Matrix.fromBlocks_apply₁₁]

include hM in
theorem rightLanguage_matrix (i j : Fin (Fintype.card (rightSupport e))) :
    (rightLanguage e L μ ν hw hμ hν).matrices 0 i j=
      rightGram B μ ν (rightCoordinate e i) (rightCoordinate e j) := by
  change (squareLanguage L 0 hp).matrices 0 _ _=_
  rw [squared_source_matrix e L B μ ν hM hw hμ hν]
  simp only [Matrix.submatrix_apply,rightCoordinate_value,Matrix.fromBlocks_apply₂₂]

def leftSourceReduction (hB : IsUnit B) :
    PromisePolyTimeTuringReduction (leftLanguage e L μ ν hw hμ hν).problem L.problem :=
  ((squareLanguage L 0 hp).supportFiniteReduction
    (square_source_symmetric e L B μ ν hM hw hμ hν) (fun _=>zero_lt_one)
    (leftSupport e) (square_left_closed e L B μ ν hM hw hμ hν)).trans
    (squareSourceReduction L 0 (source_symmetric e L B hM)
      (source_rows_nonzero e L B hM hB) (source_rows_nonproportional e L B hM hB) hp)

def rightSourceReduction (hB : IsUnit B) :
    PromisePolyTimeTuringReduction (rightLanguage e L μ ν hw hμ hν).problem L.problem :=
  ((squareLanguage L 0 hp).supportFiniteReduction
    (square_source_symmetric e L B μ ν hM hw hμ hν) (fun _=>zero_lt_one)
    (rightSupport e) (square_right_closed e L B μ ν hM hw hμ hν)).trans
    (squareSourceReduction L 0 (source_symmetric e L B hM)
      (source_rows_nonzero e L B hM hB) (source_rows_nonproportional e L B hM hB) hp)

end PlanarHom.BipartiteTensorWeight
