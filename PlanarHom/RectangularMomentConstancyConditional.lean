/- Conditional assembly lemma. All explicit hypotheses remain visible;
the final closed endpoints instantiate the required foundations. -/
import PlanarHom.RectangularSideMomentPresentation
import PlanarHom.BipartiteTensorWeightHardnessConditional

/-! Actual original-source side moments are forced constant by9.3, in one
fixed real normalized quotient. Each exponent has its own actual program. -/
noncomputable section
set_option autoImplicit false
open PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularMomentConstancy
open RectangularWeightedNormNormalization RectangularTwinQuotient
open RectangularBackgroundWeightedReconstruction RectangularSideMomentPresentation
open RectangularSourceNormSimulation (block realRectangular)
open RectangularBackgroundSourceNormSimulation (weights)
open Complexity Complexity.MixedCode AlgebraicProductInterpolation
variable {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

theorem rowMass_pos (V : Matrix X Y ℝ) (hV : ∀ i j,0<V i j)
    (μ : X→ℝ) (ν : Y→ℝ) (hμ : ∀ i,0<μ i) (hν : ∀ j,0<ν j)
    (m : ℕ) (r : Rows (normalized V μ ν)) : 0<rowMass V μ ν m r := by
  letI : Nonempty {x // Quotient.mk (rowSetoid (normalized V μ ν)) x=r} :=
    ⟨⟨r.out,Quotient.out_eq r⟩⟩
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro x _
  exact mul_pos (hμ x.val) (pow_pos (rowNorm_pos V hV ν hν x.val) _)

theorem columnMass_pos (V : Matrix X Y ℝ) (hV : ∀ i j,0<V i j)
    (μ : X→ℝ) (ν : Y→ℝ) (hμ : ∀ i,0<μ i) (hν : ∀ j,0<ν j)
    (m : ℕ) (r : Columns (normalized V μ ν)) : 0<columnMass V μ ν m r := by
  letI : Nonempty {x // Quotient.mk (columnSetoid (normalized V μ ν)) x=r} :=
    ⟨⟨r.out,Quotient.out_eq r⟩⟩
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro x _
  exact mul_pos (hν x.val) (pow_pos (columnNorm_pos V hV μ hμ x.val) _)

variable {p s d n : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)]
variable {K₀ : IntermediateField ℚ ℝ}

theorem source_moments_constant_of_potts (hPotts : PositivePottsFoundation) (basis : Module.Basis (Fin n) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j,0<(V i j:ℝ))
    (μ : Fin p→K₀) (ν : Fin s→K₀) (hμ : ∀ i,0<(μ i:ℝ)) (hν : ∀ j,0<(ν j:ℝ))
    (eR : Rows (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)))≃Boolean.Cube d)
    (eC : Columns (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)))≃Boolean.Cube d)
    (γ : ℝ) (hγ : 0<γ) (ρ : Fin d→ℝ) (hρ : ∀ r,0<ρ r ∧ ρ r≠1)
    (hcore : ∀ r s,core (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))) r s=
      γ*Boolean.tensor ρ (eR r) (eC s))
    (hnot : ¬PromisedSharpPHard
      (evaluationProblem basis (fun _:Fin 1=>block V) (fun l:Fin 0=>l.elim0) (weights μ ν)))
    (m : ℕ) :
    (∀ r s,rowMass (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m r=
      rowMass (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m s) ∧
    (∀ r s,columnMass (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m r=
      columnMass (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m s) := by
  obtain ⟨L,hM,hw,⟨red⟩⟩ := exists_moment_language basis V hV μ ν hμ hν m
  let N := normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))
  let e := (sideIndex N).trans (Equiv.sumCongr eR eC)
  let u := fun c=>rowMass (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m (eR.symm c)
  let v := fun c=>columnMass (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m (eC.symm c)
  have hu : ∀ i,0<u i := fun i=>rowMass_pos _ hV _ _ hμ hν m _
  have hv : ∀ i,0<v i := fun i=>columnMass_pos _ hV _ _ hμ hν m _
  have hm : ∀ i j,L.matrices 0 i j=
      PositiveRealCore.doubleMatrix (PositiveRealCore.scaledTensor γ ρ) (e i) (e j) := by
    intro i j
    rw [hM]
    cases hi:sideIndex N i <;> cases hj:sideIndex N j <;>
      simp [e,Equiv.trans_apply,hi,hj,BipartiteFullTwins.double,PositiveRealCore.doubleMatrix,
        PositiveRealCore.scaledTensor,hcore] <;> exact Or.inl rfl
  have hh : ∀ i,L.weights i=Sum.elim u v (e i) := by
    intro i
    rw [hw]
    cases hi:sideIndex N i with
    | inl r =>
      simp only [e,Equiv.trans_apply,hi,Equiv.sumCongr_apply,Sum.map_inl,Sum.elim_inl]
      exact congrArg (rowMass (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m)
        (eR.symm_apply_apply r).symm
    | inr r =>
      simp only [e,Equiv.trans_apply,hi,Equiv.sumCongr_apply,Sum.map_inr,Sum.elim_inr]
      exact congrArg (columnMass (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m)
        (eC.symm_apply_apply r).symm
  have hconst : (∀ i j,u i=u j) ∧ (∀ i j,v i=v j) := by
    by_contra hn
    have hn' : (∃ i j,u i≠u j) ∨ (∃ i j,v i≠v j) := by
      simpa only [not_and_or,not_forall] using hn
    exact hnot ((BipartiteTensorWeight.nonconstant_weights_hard_of_potts hPotts e L γ hγ ρ
      (fun r=>(hρ r).1) (fun r=>(hρ r).2) u v hu hv hm hh hn').trans red)
  constructor
  · intro r s
    simpa only [u,Equiv.symm_apply_apply] using hconst.1 (eR r) (eR s)
  · intro r s
    simpa only [v,Equiv.symm_apply_apply] using hconst.2 (eC r) (eC s)

/-- Once the actual normalized core chart is known, all original amplitudes
and both background vectors are reconstructed from true source programs. -/
theorem source_weighted_amplitude_tensor_of_potts (hPotts : PositivePottsFoundation) (basis : Module.Basis (Fin n) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j,0<(V i j:ℝ))
    (hinjR : Function.Injective (realRectangular V))
    (hinjC : Function.Injective (realRectangular V).transpose)
    (μ : Fin p→K₀) (ν : Fin s→K₀) (hμ : ∀ i,0<(μ i:ℝ)) (hν : ∀ j,0<(ν j:ℝ))
    (eR : Rows (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)))≃Boolean.Cube d)
    (eC : Columns (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)))≃Boolean.Cube d)
    (γ : ℝ) (hγ : 0<γ) (ρ : Fin d→ℝ) (hρ : ∀ r,0<ρ r ∧ ρ r≠1)
    (hcore : ∀ r s,core (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))) r s=
      γ*Boolean.tensor ρ (eR r) (eC s))
    (hnot : ¬PromisedSharpPHard
      (evaluationProblem basis (fun _:Fin 1=>block V) (fun l:Fin 0=>l.elim0) (weights μ ν))) :
    ∃ k l : ℕ,∃ a massX : Fin k→ℝ,∃ b massY : Fin l→ℝ,
    ∃ eX : Fin p≃Fin k×Boolean.Cube d,∃ eY : Fin s≃Fin l×Boolean.Cube d,
      0<k ∧ 0<l ∧ (∀ i,0<a i) ∧ (∀ i,0<massX i) ∧ (∀ j,0<b j) ∧ (∀ j,0<massY j) ∧
      (∀ x y,(V x y:ℝ)=a (eX x).1*b (eY y).1*Boolean.tensor ρ (eX x).2 (eY y).2) ∧
      (∀ x,(μ x:ℝ)=massX (eX x).1) ∧ (∀ y,(ν y:ℝ)=massY (eY y).1) := by
  have hm := source_moments_constant_of_potts hPotts basis V hV μ ν hμ hν eR eC γ hγ ρ hρ hcore hnot
  exact original_weighted_amplitude_tensor (realRectangular V) hV hinjR hinjC
    (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) hμ hν
    (fun r s m=>(hm m).1 r s) (fun r s m=>(hm m).2 r s) eR eC γ hγ ρ hcore

end PlanarHom.RectangularMomentConstancy
