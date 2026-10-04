import PlanarHom.UnrestrictedBasicTargetComputers
import PlanarHom.SupportBlockSemantics
import PlanarHom.FixedFieldPolynomialMachines
import PlanarHom.MixedColorEquivalence

/-! Unrestricted-input basic target algorithms. This module assembles actual
machines on endpoint-valid codes; it never enlarges a planar FP promise. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.TargetGraphDichotomy
def emptyUnaries {C K : Type} : Fin 0→C→K := fun u=>u.elim0
open Complexity Complexity.MixedCode GraphComponentCode
open ZeroOneBasicStructure ZeroOneBasicTractability
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K] {dimension : ℕ}

/-- Connected endpoint-valid input, with no planarity condition. -/
def ConnectedValid (g : MixedCode) : Prop :=
  g.Valid 1 0 ∧ (support g).Connected ∧ 0 < g.vertices

/-- The existing bipartite machine has the stronger unrestricted semantics. -/
theorem bipartite_evaluateCode_eq (side : C → Bool) (w : C → K)
    (g : MixedCode) (hg : g.Valid 1 0) :
    evaluateCode side w g = g.evaluate hg (fun _ : Fin 1 => bipartiteMatrix side)
      emptyUnaries w := by
  rw [evaluate_components]
  apply congrArg List.prod
  apply List.map_congr_left
  intro c hc
  have hv := components_valid g hg c hc
  rw [totalEvaluation_valid _ _ _ c hv]
  exact connectedValue_eq side w c hv (components_connected g hg c hc)
    (components_nonempty g c hc)

/-- Fixed basic component evaluation on all valid mixed graph words. -/
theorem basic_valid_inFP (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C → K) (h : FieldBasicZeroOneComponent M) :
    (restrictedEvaluationProblem basis (fun _ : Fin 1 => M)
      emptyUnaries w (Valid 1 0)).InFP := by
  have rankOne (a : C → K) :
      (restrictedEvaluationProblem basis (fun _ : Fin 1 => fun i j => a i * a j)
        emptyUnaries w (Valid 1 0)).InFP := by
    let e := Fintype.equivFin C
    apply (restrictedEvaluation_inFP_iff basis _ _ _ (Valid 1 0) (fun _ h => h)).mpr
    have ht := (restrictedEvaluation_inFP_iff basis _ _ _ (Valid 1 0) (fun _ h => h)).mp
      (RankOneEvaluationMachine.validEvaluation_inFP basis
        (fun i => a (e.symm i)) (fun i => w (e.symm i)))
    apply ht.congr
    intro g
    have hu : (fun l i => (emptyUnaries : Fin 0 → Fin (Fintype.card C) → K) l (e i)) =
        (emptyUnaries : Fin 0 → C → K) := by
      funext l
      exact l.elim0
    simpa only [hu, Equiv.symm_apply_apply] using
      (evaluate_color_equiv e g.val g.property
        (fun _ : Fin 1 => fun i j => a (e.symm i) * a (e.symm j))
        emptyUnaries (fun i => w (e.symm i))).symm
  rcases h with ⟨_, hone⟩ | ⟨side, _, hside⟩ | ⟨_, _, hzero⟩
  · have hm : M = fun i j => (1 : K) * 1 := by funext i j; simp [hone]
    rw [hm]
    exact rankOne (fun _ => 1)
  · have hm : M = bipartiteMatrix side := by
      funext i j
      exact hside i j
    rw [hm]
    apply (restrictedEvaluation_inFP_iff basis _ _ _ (Valid 1 0) (fun _ h => h)).mpr
    have hv : FP (encoding.restrict (Valid 1 0)) encoding Subtype.val :=
      fp_code_view _ _ _ (fun _ => rfl)
    exact (hv.comp (fp_evaluateCode basis side w)).congr
      (fun g => bipartite_evaluateCode_eq side w g.val g.property)
  · rw [hzero]
    simpa only [zero_mul] using rankOne (fun _ => 0)

/-- The fixed support-block sum is computed on connected arbitrary inputs. -/
theorem support_connected_fp (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (hs : ∀ i j, M i j = M j i) (w : C → K)
    (h : ∀ c : (RootedRestriction.colorSupport M hs).ConnectedComponent,
      FieldBasicZeroOneComponent (fun i j : c.supp => M i.val j.val)) :
    FP (encoding.restrict ConnectedValid) (numberFieldEncoding basis)
      (fun g : {g // ConnectedValid g} =>
        g.val.evaluate g.property.1 (fun _ : Fin 1 => M)
          emptyUnaries w) := by
  have hb : FP (encoding.restrict ConnectedValid) (numberFieldEncoding basis)
      (fun g : {g // ConnectedValid g} =>
        ∑ c : (RootedRestriction.colorSupport M hs).ConnectedComponent,
          g.val.evaluate g.property.1
            (fun _ : Fin 1 => fun i j : c.supp => M i.val j.val)
            emptyUnaries (fun i : c.supp => w i.val)) := by
    apply FixedFieldPolynomialMachines.fp_sum basis _ Finset.univ
    intro c _
    have hv := (restrictedEvaluation_inFP_iff basis _ _ _ (Valid 1 0)
      (fun _ h => h)).mp (basic_valid_inFP basis _ (fun i : c.supp => w i.val) (h c))
    exact hv.transportInput (ea := encoding.restrict ConnectedValid) (fun g : {g // ConnectedValid g} => ⟨g.val, g.property.1⟩)
      (fun _ => rfl)
  exact hb.congr (fun g =>
    (RootedRestriction.evaluate_eq_sum_supportBlocks g.val g.property.1
      g.property.2.1 g.property.2.2 M hs w).symm)

/-- Computing all input components, summing all fixed target components, then
multiplying gives an actual unrestricted algorithm in the original field. -/
theorem support_valid_fp (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (hs : ∀ i j, M i j = M j i) (w : C → K)
    (h : ∀ c : (RootedRestriction.colorSupport M hs).ConnectedComponent,
      FieldBasicZeroOneComponent (fun i j : c.supp => M i.val j.val)) :
    FP (encoding.restrict (Valid 1 0)) (numberFieldEncoding basis)
      (fun g : {g : MixedCode // g.Valid 1 0} =>
        g.val.evaluate g.property (fun _ : Fin 1 => M)
          emptyUnaries w) := by
  have hp (g : {g : MixedCode // g.Valid 1 0}) : ∀ c ∈ components g.val, ConnectedValid c := by
    intro c hc
    exact ⟨components_valid g.val g.property c hc,
      components_connected g.val g.property c hc, components_nonempty g.val c hc⟩
  let cs (g : {g : MixedCode // g.Valid 1 0}) : List {g // ConnectedValid g} :=
    (components g.val).attachWith ConnectedValid (hp g)
  have hc : FP (encoding.restrict (Valid 1 0)) (encoding.restrict ConnectedValid).list cs := by
    have hv : FP (encoding.restrict (Valid 1 0)) encoding Subtype.val :=
      fp_code_view _ _ _ (fun _ => rfl)
    exact (hv.comp GraphComponentMachines.fp_components).transportOutput
      (fun g => by simp [cs, BitEncoding.list, BitEncoding.restrict])
  have he := (hc.comp (ListMapMachines.fp_map _ _ _
    (support_connected_fp basis M hs w h))).comp (MaterializedFieldListMachines.fp_product basis)
  apply he.congr
  intro g
  rw [evaluate_components g.val g.property]
  apply congrArg List.prod
  simp only [Function.comp_apply, cs, List.map_attachWith]
  rw [← List.attach_map_val (l := components g.val) (f := totalEvaluation _ _ _)]
  apply List.map_congr_left
  intro c _
  exact (totalEvaluation_valid _ _ _ c.val (hp g c.val c.property).1).symm

/-- Raw unrestricted mixed evaluation uses the actual normalizer and preserves
all successful alternate input encodings. -/
theorem support_valid_inFP (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (hs : ∀ i j, M i j = M j i) (w : C → K)
    (h : ∀ c : (RootedRestriction.colorSupport M hs).ConnectedComponent,
      FieldBasicZeroOneComponent (fun i j : c.supp => M i.val j.val)) :
    (restrictedEvaluationProblem basis (fun _ : Fin 1 => M)
      emptyUnaries w (Valid 1 0)).InFP :=
  (restrictedEvaluation_inFP_iff basis _ _ _ (Valid 1 0) (fun _ h => h)).mpr
    (support_valid_fp basis M hs w h)

end PlanarHom.TargetGraphDichotomy
