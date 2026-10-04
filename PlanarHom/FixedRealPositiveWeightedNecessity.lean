import PlanarHom.FixedRealPositiveNormalization
import PlanarHom.FixedRealFiniteUnitRigidity
import PlanarHom.FixedRealQuotientTransport
import PlanarHom.PositiveWeightedAmplitudeReconstruction

/-! NEW positive-block necessity for A.12. The actual normalized row quotient
and every finite moment are computed from the original weighted source. A.6,
A.8 and A.10 force its tensor chart and constant class moments; finite weighted
Vandermonde reconstruction returns exactly the original amplitude/weight form. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealPositiveWeightedNecessity
open DensePolynomial Complexity Complexity.MixedCode RepresentedBit Boolean
open FixedRealMixedInterpolation FixedRealPositiveNormalization FixedRealActualTwins
variable {n e q b u : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K] [Algebra K ℝ]
  [Nonempty (Fin q)]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

theorem positive_block_of_not_hard (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) (old : Fin b)
    (hs : ∀ i j,M old i j=M old j i)
    (hp : ∀ i j,0<algebraMap K ℝ (M old i j)) (hi : Function.Injective (M old))
    (hw : ∀ i,0<algebraMap K ℝ (w i))
    (hn : ¬SharpPHard (problem basis M U w)) :
    Structures.AllowedWeightedBlock (fun i j => algebraMap K ℝ (M old i j))
      (fun i => algebraMap K ℝ (w i)) := by
  let P := inverseModel basis M old (fun i => hp i i)
  let C := normalizedMatrix basis M old (fun i => hp i i)
  let N := diagonalNormalize (fun i j => algebraMap K ℝ (M old i j))
  let φ : P.Carrier →+* ℝ := algebraMap P.Carrier ℝ
  have hC : ∀ i j,φ (C i j)=N i j := normalizedMatrix_real basis M old (fun i => hp i i)
  have hsN : ∀ i j,N i j=N j i :=
    diagonalNormalize_symmetric _ (fun i j => congrArg (algebraMap K ℝ) (hs i j))
  have hsC : ∀ i j,C i j=C j i := by
    intro i j
    apply φ.injective
    rw [hC,hC]
    exact hsN i j
  have hpC : ∀ i j,0<φ (C i j) := by
    intro i j
    rw [hC]
    exact diagonalNormalize_positive _ hp i j
  have hdC : ∀ i,φ (C i i)=1 := by
    intro i
    rw [hC]
    exact diagonalNormalize_diagonal _ (fun i => hp i i) i
  let wm : ℕ → Fin q → P.Carrier := fun m i => P.inclusion (w i) * P.inclusion (M old i i)^m
  have hwm : ∀ m i,φ (wm m i)=algebraMap K ℝ (w i)*(algebraMap K ℝ (M old i i))^m := by
    intro m i
    simp only [wm,φ,map_mul,map_pow,P.real_inclusion]
  have hwmp : ∀ m i,0<φ (wm m i) := by
    intro m i
    rw [hwm]
    exact mul_pos (hw i) (pow_pos (hp i i) m)
  let Q := Twins.quotientMatrix C hsC
  let v : ℕ → Quotient (Twins.rowSetoid C) → P.Carrier := fun m => Twins.quotientWeight C (wm m)
  letI : Nonempty (Quotient (Twins.rowSetoid C)) := ⟨Quotient.mk _ (Classical.choice inferInstance)⟩
  have hqs : ∀ r s,Q r s=Q s r := Twins.quotientMatrix_symmetric C hsC
  have hqp : ∀ r s,0<φ (Q r s) := by
    intro r s
    induction r using Quotient.inductionOn with
    | h i => induction s using Quotient.inductionOn with
      | h j => exact hpC i j
  have hqd : ∀ r,φ (Q r r)=1 := by
    intro r
    induction r using Quotient.inductionOn with
    | h i => exact hdC i
  have hqi : Function.Injective Q := Twins.quotientMatrix_rows_injective C hsC
  have hqwp : ∀ m r,0<φ (v m r) := fun m => quotientWeight_map_pos φ C (wm m) (hwmp m)
  have hnQ : ∀ m,¬SharpPHard (FixedRealComponents.problem P.basis (fun _ : Fin 1 => Q)
      (fun l : Fin 0 => l.elim0) (v m)) := by
    intro m hh
    have r := (quotientReduction P.basis C hsC (wm m)).trans
      (normalizedMomentReduction basis M U w old (fun i => hp i i) m)
    exact hn (hh.trans r)
  have hconst : ∀ m r s,v m r=v m s := fun m =>
    FixedRealUnitDiagonalRigidity.finite_weights_constant P.basis Q (v m)
      hqs hqp hqd hqi (hqwp m) (hnQ m)
  obtain ⟨d,a,ρ,hρ,hform⟩ := FixedRealUnitDiagonalRigidity.finite_tensor_of_not_hard
    P.basis Q (v 0) hqs hqp hqd hqi (hqwp 0) (hnQ 0)
  let er := rowEquivTo φ C N hC
  let ar := er.symm.trans a
  let ρR : Fin d → ℝ := fun r => φ (ρ r)
  have hcore : ∀ r s,Twins.quotientMatrix N hsN r s = tensor ρR (ar r) (ar s) := by
    intro r s
    have h := quotientMatrix_map_to φ C hsC N hsN hC (er.symm r) (er.symm s)
    change φ (Q (er.symm r) (er.symm s)) =
      Twins.quotientMatrix N hsN (er (er.symm r)) (er (er.symm s)) at h
    rw [er.apply_symm_apply,er.apply_symm_apply] at h
    rw [←h,hform,FixedRealLemmaA10.tensor_real]
    rfl
  have hmom : ∀ r s : Quotient (Twins.rowSetoid N), ∀ m : ℕ,
      Twins.quotientWeight N (fun i => algebraMap K ℝ (w i)*(algebraMap K ℝ (M old i i))^m) r =
      Twins.quotientWeight N (fun i => algebraMap K ℝ (w i)*(algebraMap K ℝ (M old i i))^m) s := by
    intro r s m
    have h := congrArg φ (hconst m (er.symm r) (er.symm s))
    change φ (Twins.quotientWeight C (wm m) (er.symm r)) =
      φ (Twins.quotientWeight C (wm m) (er.symm s)) at h
    rw [quotientWeight_map_to φ C N hC,quotientWeight_map_to φ C N hC] at h
    change Twins.quotientWeight N (fun i => φ (wm m i)) (er (er.symm r)) =
      Twins.quotientWeight N (fun i => φ (wm m i)) (er (er.symm s)) at h
    simpa only [er.apply_symm_apply,hwm] using h
  apply PositiveWeightedAmplitudeReconstruction.allowed_block_of_weighted_moments
    (fun i j => algebraMap K ℝ (M old i j)) hp
    (fun i j => congrArg (algebraMap K ℝ) (hs i j)) ?_ (fun i => algebraMap K ℝ (w i)) hw
    hmom ar ρR hρ hcore
  intro i j hij
  apply hi
  funext k
  exact (algebraMap K ℝ).injective (congrFun hij k)

end PlanarHom.FixedRealPositiveWeightedNecessity
