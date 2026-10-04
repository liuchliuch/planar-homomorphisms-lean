import PlanarHom.RectangularSideMomentPresentation
import PlanarHom.PositiveWeightRealAvailability
import PlanarHom.ContextualGadgetClosure
import PlanarHom.MixedColorProblemEquivalence

/-! The literal normalized rectangular core, with separate finite side charts,
acquires an actual unit-background reduction to the original weighted source.
The original backgrounds are retained as zeroth class masses until the proved
weight-removal program is applied. No source-availability hypothesis is used. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularUnitCoreSource
open RectangularTwinQuotient RectangularWeightedNormNormalization
open RectangularBackgroundWeightedReconstruction BipartiteFullTwins
open RectangularSourceNormSimulation (block block_symm realRectangular)
open RectangularBackgroundSourceNormSimulation (weights)
open Complexity Complexity.MixedCode AlgebraicProductInterpolation
open AlgebraicProductInterpolation.RealLanguage
variable {X Y : Type} [Fintype X] [Fintype Y]

/-- Zeroth moments are the original weighted masses, not fiber cardinalities. -/
theorem rowMass_zero (V : Matrix X Y ℝ) (μ : X→ℝ) (ν : Y→ℝ)
    (r : Rows (normalized V μ ν)) :
    rowMass V μ ν 0 r=∑ x : {x // Quotient.mk (rowSetoid (normalized V μ ν)) x=r},μ x.val := by
  simp [rowMass]

theorem columnMass_zero (V : Matrix X Y ℝ) (μ : X→ℝ) (ν : Y→ℝ)
    (s : Columns (normalized V μ ν)) :
    columnMass V μ ν 0 s=∑ y : {y // Quotient.mk (columnSetoid (normalized V μ ν)) y=s},ν y.val := by
  simp [columnMass]

theorem rowMass_zero_pos (V : Matrix X Y ℝ) (μ : X→ℝ) (ν : Y→ℝ)
    (hμ : ∀ x,0<μ x) (r : Rows (normalized V μ ν)) : 0<rowMass V μ ν 0 r := by
  letI : Nonempty {x // Quotient.mk (rowSetoid (normalized V μ ν)) x=r} :=
    ⟨⟨r.out,Quotient.out_eq r⟩⟩
  rw [rowMass_zero]
  exact Finset.sum_pos (fun x _=>hμ x.val) Finset.univ_nonempty

theorem columnMass_zero_pos (V : Matrix X Y ℝ) (μ : X→ℝ) (ν : Y→ℝ)
    (hν : ∀ y,0<ν y) (s : Columns (normalized V μ ν)) : 0<columnMass V μ ν 0 s := by
  letI : Nonempty {y // Quotient.mk (columnSetoid (normalized V μ ν)) y=s} :=
    ⟨⟨s.out,Quotient.out_eq s⟩⟩
  rw [columnMass_zero]
  exact Finset.sum_pos (fun y _=>hν y.val) Finset.univ_nonempty

variable [Nonempty X] [Nonempty Y]

omit [Fintype X] [Fintype Y] in
/-- Opposite-side support supplies a nonzero entry in every doubled row. -/
theorem double_rows_nonzero (C : Matrix X Y ℝ) (hC : ∀ x y,0<C x y) :
    ∀ z,double C z≠0 := by
  intro z hz
  cases z with
  | inl x => exact (ne_of_gt (hC x (Classical.arbitrary Y))) (congrFun hz (.inr (Classical.arbitrary Y)))
  | inr y => exact (ne_of_gt (hC (Classical.arbitrary X) y)) (congrFun hz (.inl (Classical.arbitrary X)))

omit [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] in
/-- Distinct sides have disjoint supports; same-side proportionality is exactly
rectangular row or column proportionality. -/
theorem double_rows_nonproportional (C : Matrix X Y ℝ) (hC : ∀ x y,0<C x y)
    (hR : ∀ x x' t,(∀ y,C x y=t*C x' y)→x=x')
    (hS : ∀ y y' t,(∀ x,C x y=t*C x y')→y=y') :
    ∀ i j,i≠j→∀t:ℝ,double C i≠t • double C j := by
  intro i j hij t he
  cases i with
  | inl x =>
    cases j with
    | inl x' =>
      apply hij
      exact congrArg Sum.inl (hR x x' t (fun y=>by
        simpa only [Pi.smul_apply,smul_eq_mul] using congrFun he (.inr y)))
    | inr y =>
      have h := congrFun he (.inr y)
      change C x y=t*0 at h
      exact (ne_of_gt (hC x y)) (by simpa using h)
  | inr y =>
    cases j with
    | inl x =>
      have h := congrFun he (.inl x)
      change C x y=t*0 at h
      exact (ne_of_gt (hC x y)) (by simpa using h)
    | inr y' =>
      apply hij
      exact congrArg Sum.inr (hS y y' t (fun x=>by
        simpa only [Pi.smul_apply,smul_eq_mul] using congrFun he (.inl x)))

/-- Each side has its own fixed chart; no equality of side cardinalities is assumed. -/
def rowIndex (N : Matrix X Y ℝ) : Fin (Fintype.card (Rows N)) ≃ Rows N :=
  (Fintype.equivFin _).symm

def columnIndex (N : Matrix X Y ℝ) : Fin (Fintype.card (Columns N)) ≃ Columns N :=
  (Fintype.equivFin _).symm

def sideFinIndex (N : Matrix X Y ℝ) :
    Fin (Fintype.card (Rows N)+Fintype.card (Columns N)) ≃ Rows N⊕Columns N :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (rowIndex N) (columnIndex N))

def finCore (N : Matrix X Y ℝ) :
    Matrix (Fin (Fintype.card (Rows N))) (Fin (Fintype.card (Columns N))) ℝ :=
  fun i j=>core N (rowIndex N i) (columnIndex N j)

omit [Nonempty X] [Nonempty Y] in
theorem finCore_positive (N : Matrix X Y ℝ) (hN : ∀ x y,0<N x y) :
    ∀ i j,0<finCore N i j := fun i j=>core_positive N hN (rowIndex N i) (columnIndex N j)

omit [Nonempty X] [Nonempty Y] in
theorem finCore_block (N : Matrix X Y ℝ) (i j) :
    block (finCore N) i j=double (core N) (sideFinIndex N i) (sideFinIndex N j) := by
  refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;>
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;>
      simp [sideFinIndex,finCore,double]

omit [Fintype Y] [Nonempty Y] in
theorem row_card_pos (N : Matrix X Y ℝ) : 0<Fintype.card (Rows N) := by
  letI : Nonempty (Rows N) := ⟨Quotient.mk _ (Classical.arbitrary X)⟩
  exact Fintype.card_pos

omit [Fintype X] [Nonempty X] in
theorem column_card_pos (N : Matrix X Y ℝ) : 0<Fintype.card (Columns N) := by
  letI : Nonempty (Columns N) := ⟨Quotient.mk _ (Classical.arbitrary Y)⟩
  exact Fintype.card_pos

theorem finCore_no_proportional_rows (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (μ : X→ℝ) (ν : Y→ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y)
    (i j) (t : ℝ) (h : ∀ k,finCore (normalized V μ ν) i k=t*finCore (normalized V μ ν) j k) :
    t=1 ∧ i=j := by
  have hc := core_no_proportional_rows V hV μ ν hμ hν
    (rowIndex _ i) (rowIndex _ j) t (fun s=>by
      simpa only [finCore,Equiv.apply_symm_apply] using h ((columnIndex _).symm s))
  exact ⟨hc.1,(rowIndex _).injective hc.2⟩

theorem finCore_no_proportional_columns (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (μ : X→ℝ) (ν : Y→ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y)
    (i j) (t : ℝ) (h : ∀ k,finCore (normalized V μ ν) k i=t*finCore (normalized V μ ν) k j) :
    t=1 ∧ i=j := by
  have hc := core_no_proportional_columns V hV μ ν hμ hν
    (columnIndex _ i) (columnIndex _ j) t (fun r=>by
      simpa only [finCore,Equiv.apply_symm_apply] using h ((rowIndex _).symm r))
  exact ⟨hc.1,(columnIndex _).injective hc.2⟩

variable {p s d : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)]
variable {K₀ : IntermediateField ℚ ℝ}

/-- The original weighted normalization supplies its own zeroth-moment source,
then the actual 3.7 program removes those positive masses. Canonical field
presentation descent and exact color reindexing preserve the original codec. -/
theorem exists_unit_core_language (basis : Module.Basis (Fin d) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j,0<(V i j:ℝ))
    (μ : Fin p→K₀) (ν : Fin s→K₀) (hμ : ∀ i,0<(μ i:ℝ)) (hν : ∀ j,0<(ν j:ℝ)) :
    ∃ U : RealLanguage
      (Fintype.card (Rows (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))))+
       Fintype.card (Columns (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))))) 1 0,
      (∀ i,U.weights i=1) ∧
      U.matrices 0=block (finCore (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)))) ∧
      Nonempty (PromisePolyTimeTuringReduction U.problem
        (evaluationProblem basis (fun _:Fin 1=>block V) (fun l:Fin 0=>l.elim0) (weights μ ν))) := by
  let N := normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))
  have hN : ∀ i j,0<N i j := normalized_pos _ hV _ _ hμ hν
  letI : Nonempty (Rows N) := ⟨Quotient.mk _ (Classical.arbitrary (Fin p))⟩
  letI : Nonempty (Columns N) := ⟨Quotient.mk _ (Classical.arbitrary (Fin s))⟩
  obtain ⟨QL,hM,hw,⟨rq⟩⟩ := RectangularSideMomentPresentation.exists_moment_language basis V hV μ ν hμ hν 0
  have hsQ : ∀ i j,QL.matrices 0 i j=QL.matrices 0 j i := by
    intro i j
    rw [hM,hM]
    exact double_symmetric _ _ _
  have hwQ : ∀ i,0<QL.weights i := by
    intro i
    rw [hw]
    cases RectangularSideMomentPresentation.sideIndex N i with
    | inl r => exact rowMass_zero_pos _ _ _ hμ r
    | inr c => exact columnMass_zero_pos _ _ _ hν c
  have hnzQ : ∀ i,QL.matrices 0 i≠0 := by
    intro i hi
    apply double_rows_nonzero (core N) (core_positive N hN) (RectangularSideMomentPresentation.sideIndex N i)
    funext z
    have hz := congrFun hi ((RectangularSideMomentPresentation.sideIndex N).symm z)
    simpa only [hM,N,Equiv.apply_symm_apply,Pi.zero_apply] using hz
  have hproj : ∀ i j,i≠j→∀ t:ℝ,QL.matrices 0 i≠t • QL.matrices 0 j := by
    intro i j hij t he
    apply double_rows_nonproportional (core N) (core_positive N hN)
      (fun r r' t hh=>(core_no_proportional_rows _ hV _ _ hμ hν r r' t hh).2)
      (fun c c' t hh=>(core_no_proportional_columns _ hV _ _ hμ hν c c' t hh).2)
      (RectangularSideMomentPresentation.sideIndex N i) (RectangularSideMomentPresentation.sideIndex N j)
      (fun h=>hij ((RectangularSideMomentPresentation.sideIndex N).injective h)) t
    funext z
    have hz := congrFun he ((RectangularSideMomentPresentation.sideIndex N).symm z)
    simpa only [Pi.smul_apply,smul_eq_mul,hM,N,Equiv.apply_symm_apply] using hz
  let e := (sideFinIndex N).trans (RectangularSideMomentPresentation.sideIndex N).symm
  let A := fun l i j=>QL.matrices l (e i) (e j)
  let U := unitLanguage A (fun l i j=>QL.matrices_algebraic l (e i) (e j))
  have present := U.presentationDescentReduction QL.field QL.basis
    (fun l i j=>QL.matricesK l (e i) (e j)) (fun l:Fin 0=>l.elim0) (fun _=>1)
    (fun _ _ _=>rfl) (fun l=>l.elim0) (fun _=>rfl)
  have hc := evaluationProblem_color_equiv QL.basis e QL.matricesK QL.unariesK (fun _=>1)
  have hu : (fun l:Fin 0=>l.elim0)=(fun l i=>QL.unariesK l (e i)) := by
    funext l
    exact l.elim0
  rw [hu,hc] at present
  have rU := present.trans (QL.lemma37_removeWeights 0 hsQ hwQ hnzQ hproj _ rq)
  refine ⟨U,(fun _=>rfl),?_,⟨rU⟩⟩
  funext i j
  change QL.matrices 0 (e i) (e j)=block (finCore N) i j
  rw [hM,finCore_block]
  simp only [e,Equiv.trans_apply,N,Equiv.apply_symm_apply]

end PlanarHom.RectangularUnitCoreSource
