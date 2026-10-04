import PlanarHom.FixedRealRectangularCoreSources
import PlanarHom.FixedRealRectangularRigidity
import PlanarHom.BipartiteWeightedSourceFormsConditional

/-! NEW complete rectangular weighted necessity for A.12. Every paired moment
is an actual original-source query; full A.11 forces each side separately
constant regardless of the other side's positive moment vector. The two finite
Vandermonde reconstructions recover the original amplitudes and weights. -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical
namespace PlanarHom.FixedRealRectangularWeightedNecessity
open DensePolynomial Complexity RepresentedBit Boolean Structures
open RectangularSourceNormSimulation RectangularBackgroundSourceNormSimulation
open RectangularWeightedNormNormalization RectangularTwinQuotient RectangularBackgroundWeightedReconstruction
variable {n e p s : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K] [Algebra K ℝ]
variable [Nonempty (Fin p)] [Nonempty (Fin s)]

 theorem allowed_of_not_hard (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (V : Matrix (Fin p) (Fin s) K) (μ : Fin p → K) (ν : Fin s → K)
    (hV : ∀ i j,0<algebraMap K ℝ (V i j)) (hi : Function.Injective (block V))
    (hμ : ∀ i,0<algebraMap K ℝ (μ i)) (hν : ∀ j,0<algebraMap K ℝ (ν j))
    (hn : ¬SharpPHard (FixedRealComponents.problem basis (fun _ : Fin 1 => block V)
      (fun l : Fin 0 => l.elim0) (weights μ ν))) :
    AllowedWeightedBlock (fun i j => algebraMap K ℝ (block V i j))
      (fun i => algebraMap K ℝ (weights μ ν i)) := by
  let VR : Matrix (Fin p) (Fin s) ℝ := fun i j => algebraMap K ℝ (V i j)
  let μR := fun i => algebraMap K ℝ (μ i)
  let νR := fun j => algebraMap K ℝ (ν j)
  let N := normalized VR μR νR
  let P := FixedRealRectangularNormalization.model basis V hV μ ν hμ hν
  obtain ⟨R,μm,νm,hR,hμm,hνm,red⟩ := FixedRealRectangularCoreSources.exists_core_sources basis V hV μ ν hμ hν
  letI : Nonempty (Rows N) := ⟨Quotient.mk _ (Classical.choice inferInstance)⟩
  letI : Nonempty (Columns N) := ⟨Quotient.mk _ (Classical.choice inferInstance)⟩
  have hRreal : FixedRealRectangularRigidity.realR R=core N := funext (fun r => funext (hR r))
  have hp : ∀ r s,0<FixedRealRectangularRigidity.realR R r s := by
    rw [hRreal]
    exact core_positive N (normalized_pos VR hV μR νR hμ hν)
  have hrows : ∀ r r',r≠r'→∀t:ℝ,FixedRealRectangularRigidity.realR R r≠t • FixedRealRectangularRigidity.realR R r' := by
    rw [hRreal]
    intro r r' hne t he
    apply hne
    exact (core_no_proportional_rows VR hV μR νR hμ hν r r' t (fun s => congrFun he s)).2
  have hcols : ∀ r r',r≠r'→∀t:ℝ,(FixedRealRectangularRigidity.realR R).transpose r≠t • (FixedRealRectangularRigidity.realR R).transpose r' := by
    rw [hRreal]
    intro r r' hne t he
    apply hne
    exact (core_no_proportional_columns VR hV μR νR hμ hν r r' t (fun s => congrFun he s)).2
  have hmpos : ∀ m r,0<algebraMap P.Carrier ℝ (μm m r) := by
    intro m r
    rw [hμm]
    exact RectangularMomentConstancy.rowMass_pos VR hV μR νR hμ hν m r
  have hnpos : ∀ m r,0<algebraMap P.Carrier ℝ (νm m r) := by
    intro m r
    rw [hνm]
    exact RectangularMomentConstancy.columnMass_pos VR hV μR νR hμ hν m r
  have hnot : ∀ m,¬SharpPHard (FixedRealRectangularRigidity.problem P.basis R (μm m) (νm m)) := by
    intro m hh
    exact hn (hh.trans (Classical.choice (red m)))
  obtain ⟨d,eX,eY,c,ρ,hc,hρ,hform,_,_⟩ := FixedRealRectangularRigidity.rigidity_of_not_hard
    P.basis R (μm 0) (νm 0) hp hrows hcols (hmpos 0) (hnpos 0) (hnot 0)
  have hconst := fun m => FixedRealRectangularRigidity.weights_constant_of_chart P.basis R
    (μm m) (νm m) eX eY c ρ hc hρ hform (hmpos m) (hnpos m) (hnot m)
  have hmX : ∀ r s,∀m:ℕ,rowMass VR μR νR m r=rowMass VR μR νR m s := by
    intro r s m
    exact (hμm m r).symm.trans ((congrArg (algebraMap P.Carrier ℝ) ((hconst m).1 r s)).trans (hμm m s))
  have hmY : ∀ r s,∀m:ℕ,columnMass VR μR νR m r=columnMass VR μR νR m s := by
    intro r s m
    exact (hνm m r).symm.trans ((congrArg (algebraMap P.Carrier ℝ) ((hconst m).2 r s)).trans (hνm m s))
  have hcore : ∀ r s,core N r s=algebraMap P.Carrier ℝ c *
      tensor (fun i => algebraMap P.Carrier ℝ (ρ i)) (eX r) (eY s) := by
    intro r s
    rw [←hR,hform,map_mul,FixedRealLemmaA10.tensor_real]
  have hir : Function.Injective VR := by
    intro i j hij
    have he : Fin.castAdd s i=Fin.castAdd s j := hi (by
      funext k
      refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simp only [block_left_left]
      · simp only [block_left_right]
        exact (algebraMap K ℝ).injective (congrFun hij k))
    apply Fin.ext
    exact congrArg (fun x : Fin (p+s) => x.val) he
  have hic : Function.Injective VR.transpose := by
    intro i j hij
    have he : Fin.natAdd p i=Fin.natAdd p j := hi (by
      funext k
      refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simp only [block_right_left]
        exact (algebraMap K ℝ).injective (congrFun hij k)
      · simp only [block_right_right])
    apply Fin.ext
    have hh := congrArg (fun x : Fin (p+s) => x.val) he
    dsimp at hh
    omega
  obtain ⟨k,l,a,massX,b,massY,fX,fY,hk,hl,ha,hmx,hb,hmy,hval,hx,hy⟩ :=
    original_weighted_amplitude_tensor VR hV hir hic μR νR hμ hν hmX hmY eX eY
      (algebraMap P.Carrier ℝ c) hc (fun i => algebraMap P.Carrier ℝ (ρ i)) hcore
  have done := BipartiteWeightedSourceForms.allowedWeighted_of_amplitudes VR μR νR a massX b massY
    (fun i => algebraMap P.Carrier ℝ (ρ i)) hk hl ha hb hmx hmy hρ fX fY hval hx hy
  have hmatrix : (fun i j => algebraMap K ℝ (block V i j))=block VR := by
    funext i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp only [block_left_left,block_left_right,block_right_left,block_right_right,map_zero,VR]
  have hweights : (fun i => algebraMap K ℝ (weights μ ν i))=weights μR νR := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;>
      simp only [weights,Fin.addCases_left,Fin.addCases_right,μR,νR]
  rwa [hmatrix,hweights]

end PlanarHom.FixedRealRectangularWeightedNecessity
