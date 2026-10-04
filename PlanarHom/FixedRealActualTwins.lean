import PlanarHom.FixedRealZeroWeightDeletion
import PlanarHom.Quotient
import PlanarHom.RootedHomogeneousSemantics
import Mathlib.Data.Fintype.Quotient

/-! NEW: actual identical-row aggregation in the represented fixed-real model.
Both directions query exactly the original graph and preserve arbitrary valid
answer representatives. The quotient retains the zero row and sums the actual
original vertex weights. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealActualTwins
open DensePolynomial Complexity Complexity.MixedCode RepresentedBit
variable {d e : ℕ} {K C D : Type} [Field K] [Algebra (RationalFunction d) K]
  [Fintype C] [Fintype D]
variable (basis : Module.Basis (Fin e) (RationalFunction d) K)

def homogeneousReduction (M : Matrix C C K) (w : C → K)
    (N : Matrix D D K) (v : D → K)
    (he : ∀ (g : MixedCode) (hg : g.Valid 1 0),
      (g.toMultiGraph hg).partition N v = (g.toMultiGraph hg).partition M w) :
    Reduction (FixedRealComponents.problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)
      (FixedRealComponents.problem basis (fun _ : Fin 1 => N) (fun l : Fin 0 => l.elim0) v) :=
  FixedRealZeroWeights.sameGraphReduction basis _ _ _ _ _ _
    (fun g hg => by simpa only [evaluate_homogeneous] using he g hg)

def quotientReduction (A : Matrix C C K) (hs : ∀ i j, A i j = A j i) (w : C → K) :
    Reduction (FixedRealComponents.problem basis (fun _ : Fin 1 => Twins.quotientMatrix A hs)
      (fun l : Fin 0 => l.elim0) (Twins.quotientWeight A w))
      (FixedRealComponents.problem basis (fun _ : Fin 1 => A) (fun l : Fin 0 => l.elim0) w) :=
  homogeneousReduction basis _ _ A w
    (fun g hg => Twins.partition_canonicalQuotient (g.toMultiGraph hg) A w hs)

def originalReduction (A : Matrix C C K) (hs : ∀ i j, A i j = A j i) (w : C → K) :
    Reduction (FixedRealComponents.problem basis (fun _ : Fin 1 => A) (fun l : Fin 0 => l.elim0) w)
      (FixedRealComponents.problem basis (fun _ : Fin 1 => Twins.quotientMatrix A hs)
        (fun l : Fin 0 => l.elim0) (Twins.quotientWeight A w)) :=
  homogeneousReduction basis A w _ _
    (fun g hg => (Twins.partition_canonicalQuotient (g.toMultiGraph hg) A w hs).symm)

def reindexReduction (M : Matrix D D K) (w : D → K) (a : C ≃ D) :
    Reduction (FixedRealComponents.problem basis (fun _ : Fin 1 => fun i j => M (a i) (a j))
      (fun l : Fin 0 => l.elim0) (fun i => w (a i)))
      (FixedRealComponents.problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w) :=
  homogeneousReduction basis _ _ M w
    (fun g hg => ((g.toMultiGraph hg).partition_reindexColors M w a).symm)

/-- Field embeddings identify exactly the same actual row classes. -/
def rowEquiv (φ : K →+* ℝ) (A : Matrix C C K) :
    Quotient (Twins.rowSetoid A) ≃ Quotient (Twins.rowSetoid (fun i j => φ (A i j))) where
  toFun := Quotient.map id (by intro i j h k; exact congrArg φ (h k))
  invFun := Quotient.map id (by intro i j h k; exact φ.injective (h k))
  left_inv x := Quotient.inductionOn x (fun _ => rfl)
  right_inv x := Quotient.inductionOn x (fun _ => rfl)

@[simp] theorem rowEquiv_mk (φ : K →+* ℝ) (A : Matrix C C K) (i : C) :
    rowEquiv φ A (Quotient.mk _ i) = Quotient.mk _ i := rfl

theorem quotientMatrix_map (φ : K →+* ℝ) (A : Matrix C C K)
    (hs : ∀ i j, A i j = A j i) (x y : Quotient (Twins.rowSetoid A)) :
    φ (Twins.quotientMatrix A hs x y) =
      Twins.quotientMatrix (fun i j => φ (A i j)) (fun i j => congrArg φ (hs i j))
        (rowEquiv φ A x) (rowEquiv φ A y) := by
  induction x using Quotient.inductionOn with
  | h i => induction y using Quotient.inductionOn with
    | h j => rfl

theorem quotientWeight_map (φ : K →+* ℝ) (A : Matrix C C K) (w : C → K)
    (x : Quotient (Twins.rowSetoid A)) :
    φ (Twins.quotientWeight A w x) =
      Twins.quotientWeight (fun i j => φ (A i j)) (fun i => φ (w i)) (rowEquiv φ A x) := by
  have hp : ∀ i, (Quotient.mk (Twins.rowSetoid A) i = x) ↔
      (Quotient.mk (Twins.rowSetoid (fun i j => φ (A i j))) i = rowEquiv φ A x) := by
    intro i
    constructor
    · intro h
      exact congrArg (rowEquiv φ A) h
    · intro h
      exact (rowEquiv φ A).injective h
  unfold Twins.quotientWeight
  rw [map_sum]
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight hp) _ _ (fun _ => rfl)

end PlanarHom.FixedRealActualTwins
