-- Necessity and literal-form extraction; Ising FP endpoints are assembled separately.
/- Conditional assembly lemma. All explicit hypotheses remain visible;
the final closed endpoints instantiate the required foundations. -/
import PlanarHom.RectangularMomentConstancyConditional
import PlanarHom.CommonAmplitudeCoordinates
import PlanarHom.TractableBlockFormsDefinition
import PlanarHom.AlgebraicLanguagePresentation

/-! Original unweighted rectangular tensor forms, with independent side charts.
Equal source moments are obtained from the actual original evaluation problem.
Repeated and proportional original rows and columns are permitted throughout. -/
noncomputable section
set_option autoImplicit false
open PlanarHom.AlgebraicProductInterpolation.RealLanguage
set_option maxHeartbeats 600000
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularUnweightedSourceForms
open Boolean RectangularWeightedNormNormalization RectangularTwinQuotient
open RectangularBackgroundWeightedReconstruction CommonAmplitudeCoordinates
open RectangularSourceNormSimulation (block realRectangular)
open RectangularBackgroundSourceNormSimulation (weights)
open Complexity Complexity.MixedCode AlgebraicProductInterpolation

/-- The displayed original-source form: a positive rectangular rank-one factor
and a positive Ising tensor, with independent bijections on its two sides.
The tensor may be empty, and parameters equal to one are allowed. -/
def RectangularTensorForm {X Y : Type} (V : Matrix X Y ℝ) : Prop :=
  ∃ k l d : ℕ, ∃ eX : X ≃ Fin k × Cube d, ∃ eY : Y ≃ Fin l × Cube d,
    ∃ a : Fin k → ℝ, ∃ b : Fin l → ℝ, ∃ ρ : Fin d → ℝ,
      0<k ∧ 0<l ∧ (∀ i,0<a i) ∧ (∀ j,0<b j) ∧ (∀ r,0<ρ r) ∧
      ∀ x y,V x y=a (eX x).1*b (eY y).1*tensor ρ (eX x).2 (eY y).2

abbrev literalTensorForm {X Y : Type} (V : Matrix X Y ℝ) : Prop := RectangularTensorForm V

variable {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] {d : ℕ}

omit [Nonempty X] [Nonempty Y] in
/-- At unit backgrounds the source-program normalization is exactly the
ordinary rectangular norm normalization. -/
theorem normalized_unit_eq (V : Matrix X Y ℝ) :
    normalized V (fun _=>1) (fun _=>1)=RectangularNormNormalization.normalized V := by
  ext x y
  simp [normalized,rowNorm,columnNorm,RectangularNormNormalization.normalized,
    RectangularNormNormalization.rowNorm,RectangularNormNormalization.columnNorm]

/-- Unit-background reconstruction uses moment multisets, so duplicate original
amplitudes need no injectivity hypothesis. The quotient is the actual weighted
normalization at unit weights, matching the source-moment program exactly. -/
theorem original_unit_amplitude_tensor (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (hmX : ∀ r s : Rows (normalized V (fun _=>1) (fun _=>1)),∀ m : ℕ,
      rowMass V (fun _=>1) (fun _=>1) m r=rowMass V (fun _=>1) (fun _=>1) m s)
    (hmY : ∀ r s : Columns (normalized V (fun _=>1) (fun _=>1)),∀ m : ℕ,
      columnMass V (fun _=>1) (fun _=>1) m r=columnMass V (fun _=>1) (fun _=>1) m s)
    (eR : Rows (normalized V (fun _=>1) (fun _=>1)) ≃ Cube d)
    (eC : Columns (normalized V (fun _=>1) (fun _=>1)) ≃ Cube d)
    (γ : ℝ) (hγ : 0<γ) (ρ : Fin d → ℝ)
    (hcore : ∀ r s,core (normalized V (fun _=>1) (fun _=>1)) r s=γ*tensor ρ (eR r) (eC s)) :
    ∃ k l : ℕ,∃ a : Fin k → ℝ,∃ b : Fin l → ℝ,
    ∃ eX : X ≃ Fin k×Cube d,∃ eY : Y ≃ Fin l×Cube d,
      0<k ∧ 0<l ∧ (∀ i,0<a i) ∧ (∀ j,0<b j) ∧
        ∀ x y,V x y=a (eX x).1*b (eY y).1*tensor ρ (eX x).2 (eY y).2 := by
  let rmap : X → Rows (normalized V (fun _=>1) (fun _=>1)) := Quotient.mk _
  let cmap : Y → Columns (normalized V (fun _=>1) (fun _=>1)) := Quotient.mk _
  have hr : Function.Surjective rmap := fun r => ⟨r.out,Quotient.out_eq r⟩
  have hc : Function.Surjective cmap := fun s => ⟨s.out,Quotient.out_eq s⟩
  letI : Nonempty (Rows (normalized V (fun _=>1) (fun _=>1))) := ⟨rmap (Classical.arbitrary X)⟩
  letI : Nonempty (Columns (normalized V (fun _=>1) (fun _=>1))) := ⟨cmap (Classical.arbitrary Y)⟩
  obtain ⟨k,a,ex,hk,ha,hex,hax⟩ := exists_common_amplitude_chart rmap hr
    (rowNorm V (fun _=>1)) (rowNorm_pos V hV _ (fun _=>zero_lt_one)) (by
      intro s t m
      convert hmX s t m using 1 <;>
        apply Finset.sum_congr (by ext x; simp) <;> intro x hx <;> simp)
  obtain ⟨l,b,ey,hl,hb,hey,hby⟩ := exists_common_amplitude_chart cmap hc
    (columnNorm V (fun _=>1)) (columnNorm_pos V hV _ (fun _=>zero_lt_one)) (by
      intro s t m
      convert hmY s t m using 1 <;>
        apply Finset.sum_congr (by ext x; simp) <;> intro x hx <;> simp)
  let eX : X ≃ Fin k×Cube d := ex.trans
    ((Equiv.prodCongr eR (Equiv.refl (Fin k))).trans (Equiv.prodComm _ _))
  let eY : Y ≃ Fin l×Cube d := ey.trans
    ((Equiv.prodCongr eC (Equiv.refl (Fin l))).trans (Equiv.prodComm _ _))
  refine ⟨k,l,(fun i=>γ*a i),b,eX,eY,hk,hl,(fun i=>mul_pos hγ (ha i)),hb,?_⟩
  intro x y
  have hsource : V x y=rowNorm V (fun _=>1) x*columnNorm V (fun _=>1) y*
      core (normalized V (fun _=>1) (fun _=>1)) (rmap x) (cmap y) := by
    change V x y=rowNorm V (fun _=>1) x*columnNorm V (fun _=>1) y*
      core (normalized V (fun _=>1) (fun _=>1)) (Quotient.mk _ x) (Quotient.mk _ y)
    rw [core_entry]
    exact reconstruct V hV _ _ (fun _=>zero_lt_one) (fun _=>zero_lt_one) x y
  have hv := hsource.trans
    (congrArg₂ (fun u v : ℝ=>u*v)
      (congrArg₂ (fun u v : ℝ=>u*v) (hax x) (hby y)) (hcore (rmap x) (cmap y)))
  change V x y=(γ*a (ex x).2)*b (ey y).2*tensor ρ (eR (ex x).1) (eC (ey y).1)
  have heq : tensor ρ (eR (ex x).1) (eC (ey y).1)=tensor ρ (eR (rmap x)) (eC (cmap y)) :=
    congrArg₂ (tensor ρ) (congrArg eR (hex x)) (congrArg eC (hey y))
  rw [heq]
  exact hv.trans (by ring)

variable {p s k l n : ℕ}

def sumProductEquiv : ((Fin k×Cube d)⊕(Fin l×Cube d)) ≃ (Fin k⊕Fin l)×Cube d where
  toFun := Sum.elim (fun z=>(Sum.inl z.1,z.2)) (fun z=>(Sum.inr z.1,z.2))
  invFun := fun z=>Sum.elim (fun a=>Sum.inl (a,z.2)) (fun b=>Sum.inr (b,z.2)) z.1
  left_inv := by intro z; cases z <;> rfl
  right_inv := by rintro ⟨z,c⟩; cases z <;> rfl

def colorChart (eX : Fin p≃Fin k×Cube d) (eY : Fin s≃Fin l×Cube d) :
    Fin (p+s) ≃ (Fin k⊕Fin l)×Cube d :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr eX eY).trans sumProductEquiv)

/-- Literal rectangular amplitudes assemble the tractable symmetric block. -/
theorem block_form_of_amplitudes (V : Matrix (Fin p) (Fin s) ℝ)
    (a : Fin k→ℝ) (b : Fin l→ℝ) (ρ : Fin d→ℝ)
    (hk : 0<k) (hl : 0<l) (ha : ∀ i,0<a i) (hb : ∀ j,0<b j) (hρ : ∀ r,0<ρ r)
    (eX : Fin p≃Fin k×Cube d) (eY : Fin s≃Fin l×Cube d)
    (hV : ∀ i j,V i j=a (eX i).1*b (eY j).1*tensor ρ (eX i).2 (eY j).2) :
    TractableBlockComposition.Form (block V) := by
  refine .bipartite ⟨0,hk⟩ ⟨0,hl⟩ (colorChart eX eY) a ha b hb ρ hρ ?_
  apply Matrix.ext
  intro i j
  obtain ⟨i,rfl⟩ := (colorChart eX eY).surjective i
  obtain ⟨j,rfl⟩ := (colorChart eX eY).surjective j
  simp only [Matrix.reindex_apply]
  refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;>
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;>
    simp [block,colorChart,sumProductEquiv,MultiGraph.tensorInteraction,hV,tensor_symm,mul_comm]

theorem block_form (V : Matrix (Fin p) (Fin s) ℝ) (hform : RectangularTensorForm V) :
    TractableBlockComposition.Form (block V) := by
  obtain ⟨k,l,d,eX,eY,a,b,ρ,hk,hl,ha,hb,hρ,hV⟩ := hform
  exact block_form_of_amplitudes V a b ρ hk hl ha hb hρ eX eY hV

variable [Nonempty (Fin p)] [Nonempty (Fin s)] {K₀ : IntermediateField ℚ ℝ}

/-- The hard direction remaining after the actual normalized-core tensor chart:
source non-hardness forces literal original amplitudes, including repeats. -/
theorem source_form_of_core_of_potts (hPotts : PositivePottsFoundation) (basis : Module.Basis (Fin n) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j,0<(V i j:ℝ))
    (eR : Rows (normalized (realRectangular V) (fun _=>1) (fun _=>1))≃Cube d)
    (eC : Columns (normalized (realRectangular V) (fun _=>1) (fun _=>1))≃Cube d)
    (γ : ℝ) (hγ : 0<γ) (ρ : Fin d→ℝ) (hρ : ∀ r,0<ρ r ∧ ρ r≠1)
    (hcore : ∀ r s,core (normalized (realRectangular V) (fun _=>1) (fun _=>1)) r s=
      γ*tensor ρ (eR r) (eC s))
    (hnot : ¬PromisedSharpPHard
      (evaluationProblem basis (fun _:Fin 1=>block V) (fun u:Fin 0=>u.elim0) (fun _=>1))) :
    RectangularTensorForm (realRectangular V) := by
  have hw : weights (fun _:Fin p=>(1:K₀)) (fun _:Fin s=>(1:K₀))=(fun _=>1) := by
    funext i
    refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;> simp [RectangularBackgroundSourceNormSimulation.weights]
  have hn : ¬PromisedSharpPHard
      (evaluationProblem basis (fun _:Fin 1=>block V) (fun u:Fin 0=>u.elim0)
        (weights (fun _=>1) (fun _=>1))) := by simpa only [hw] using hnot
  have hm := RectangularMomentConstancy.source_moments_constant_of_potts hPotts basis V hV
    (fun _=>1) (fun _=>1) (fun _=>zero_lt_one) (fun _=>zero_lt_one)
    eR eC γ hγ ρ hρ hcore hn
  obtain ⟨k,l,a,b,eX,eY,hk,hl,ha,hb,hval⟩ := original_unit_amplitude_tensor
    (realRectangular V) hV (fun r s m=>(hm m).1 r s) (fun r s m=>(hm m).2 r s)
    eR eC γ hγ ρ hcore
  exact ⟨k,l,d,eX,eY,a,b,ρ,hk,hl,ha,hb,(fun r=>(hρ r).1),hval⟩

/-- The canonical original-language non-hardness endpoint. Only the true
normalized-core chart remains a structural hypothesis; original class moments
and common amplitudes are obtained from actual source programs. -/
theorem source_language_form_of_core_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage (p+s) 1 0)
    (V : Matrix (Fin p) (Fin s) ℝ) (hV : ∀ i j,0<V i j)
    (hM : ∀ i j,L.matrices 0 i j=block V i j) (hunit : ∀ i,L.weights i=1)
    (eR : Rows (normalized V (fun _=>1) (fun _=>1))≃Cube d)
    (eC : Columns (normalized V (fun _=>1) (fun _=>1))≃Cube d)
    (γ : ℝ) (hγ : 0<γ) (ρ : Fin d→ℝ) (hρ : ∀ r,0<ρ r ∧ ρ r≠1)
    (hcore : ∀ r s,core (normalized V (fun _=>1) (fun _=>1)) r s=
      γ*tensor ρ (eR r) (eC s)) (hnot : ¬PromisedSharpPHard L.problem) :
    RectangularTensorForm V := by
  let VK : Matrix (Fin p) (Fin s) L.field :=
    fun i j=>L.matricesK 0 (Fin.castAdd s i) (Fin.natAdd p j)
  have hVK : realRectangular VK=V := by
    funext i j
    exact (hM (Fin.castAdd s i) (Fin.natAdd p j)).trans (by simp)
  have hMK : ∀ l i j,(block VK i j:ℝ)=L.matrices l i j := by
    intro l i j
    have hl : l=0 := Subsingleton.elim _ _
    subst l
    rw [hM]
    refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;>
      refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;>
      simp [block,←hVK,realRectangular]
  have red := L.presentationMapReduction L.field L.basis (fun _:Fin 1=>block VK)
    (fun u:Fin 0=>u.elim0) (fun _=>1) hMK (fun u=>u.elim0)
    (fun i=>(hunit i).symm)
  have hn : ¬PromisedSharpPHard
      (evaluationProblem L.basis (fun _:Fin 1=>block VK) (fun u:Fin 0=>u.elim0) (fun _=>1)) :=
    fun hh=>hnot (hh.trans red)
  subst V
  exact source_form_of_core_of_potts hPotts L.basis VK hV eR eC γ hγ ρ hρ hcore hn

end PlanarHom.RectangularUnweightedSourceForms
