import PlanarHom.FixedRealPositiveWeightedNecessity
import PlanarHom.FixedRealSupportRestriction
import PlanarHom.WeightedSupportClassAssembly
import Mathlib.Algebra.Order.Ring.InjSurj

/-! NEW weighted support-component extraction and finite-color positive-block
necessity. The induced real order is used only in the finite rooted algebra;
the actual input/output programs remain represented bit programs. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealWeightedSupportSources
open DensePolynomial Complexity RepresentedBit RootedRestriction
variable {n e : ℕ} {K C : Type} [Field K] [Algebra (RationalFunction n) K] [Algebra K ℝ] [Fintype C]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

def submatrixReduction (M : Matrix C C K) (hs : ∀ i j,M i j=M j i) (w : C → K)
    (hw : ∀ i,0<algebraMap K ℝ (w i)) (X : Set C) (hX : ColorClosed M X) :
    Reduction (FixedRealComponents.problem basis (fun _ : Fin 1 => fun i j : X => M i.val j.val)
      (fun l : Fin 0 => l.elim0) (fun i : X => w i.val))
      (FixedRealComponents.problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w) := by
  let φ : K →+* ℝ := algebraMap K ℝ
  letI : LinearOrder K := LinearOrder.lift' φ φ.injective
  letI : IsStrictOrderedRing K := Function.Injective.isStrictOrderedRing φ φ.map_zero φ.map_one
    φ.map_add φ.map_mul (fun {_ _} => Iff.rfl) (fun {_ _} => Iff.rfl)
  have hwK : ∀ i,0<w i := by
    intro i
    change φ 0<φ (w i)
    simpa only [map_zero] using hw i
  exact FixedRealRootRestriction.submatrixReduction basis M hs w hwK X hX

theorem submatrix_rows_injective (M : Matrix C C K) (hi : Function.Injective M)
    (X : Set C) (hX : ColorClosed M X) :
    Function.Injective (fun i j : X => M i.val j.val) := by
  intro i j he
  apply Subtype.ext
  apply hi
  funext k
  by_cases hk : k∈X
  · exact congrFun he ⟨k,hk⟩
  · have hz : ∀ x : X,M x.val k=0 := fun x => by
      by_contra h
      exact hk (hX x.val x.property k h)
    rw [hz i,hz j]

variable [Nonempty C]

theorem positive_block_of_not_hard (M : Matrix C C K) (w : C → K)
    (hs : ∀ i j,M i j=M j i) (hp : ∀ i j,0<algebraMap K ℝ (M i j))
    (hi : Function.Injective M) (hw : ∀ i,0<algebraMap K ℝ (w i))
    (hn : ¬SharpPHard (FixedRealComponents.problem basis
      (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) :
    Structures.AllowedWeightedBlock (fun i j => algebraMap K ℝ (M i j)) (fun i => algebraMap K ℝ (w i)) := by
  let f : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  letI : Nonempty (Fin (Fintype.card C)) := ⟨f.symm (Classical.choice inferInstance)⟩
  have red := FixedRealActualTwins.reindexReduction basis M w f
  have hi' : Function.Injective (fun i j => M (f i) (f j)) := by
    intro i j hij
    apply f.injective
    apply hi
    funext k
    simpa only [f.apply_symm_apply] using congrFun hij (f.symm k)
  have hh := FixedRealPositiveWeightedNecessity.positive_block_of_not_hard basis
    (fun _ : Fin 1 => fun i j => M (f i) (f j)) (fun l : Fin 0 => l.elim0) (fun i => w (f i)) 0
    (fun i j => hs _ _) (fun i j => hp _ _) hi' (fun i => hw _) (fun h => hn (h.trans red))
  exact Structures.AllowedWeightedBlock.of_equiv f hh

end PlanarHom.FixedRealWeightedSupportSources
