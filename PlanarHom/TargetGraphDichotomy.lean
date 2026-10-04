import PlanarHom.TargetGraphDichotomyCodes
import PlanarHom.ZeroOneNaturalHardnessClosed

/-! Corollary 12.1 for all finite undirected targets, loops permitted and no
parallel target edges. General-graph hardness follows from the proved planar
hardness, and general-graph tractability is established by actual machines;
Dyer--Greenhill is not assumed. -/
noncomputable section
open Classical
namespace PlanarHom.TargetGraphDichotomy
open Complexity ZeroOneBasicStructure ZeroOneBasicTractability AlgebraicProductInterpolation

/-- A Boolean adjacency table is exactly a finite undirected target with at
most one edge for each unordered pair, including diagonal loops. -/
structure Target (q : ℕ) where
  adjacent : Fin q → Fin q → Bool
  symmetric : ∀ i j, adjacent i j = adjacent j i

/-- Literal graph forms: fully looped clique; loopless complete bipartite with
both sides nonempty; or one isolated loopless vertex. -/
def ComponentBasic {C : Type*} (R : C → C → Bool) : Prop :=
  (Nonempty C ∧ ∀ i j, R i j = true) ∨
  (∃ side : C → Bool, Function.Surjective side ∧
    ∀ i j, R i j = decide (side i ≠ side j)) ∨
  (Nonempty C ∧ Subsingleton C ∧ ∀ i j, R i j = false)

/-- The adjacency-matrix and graph-theoretic lists agree in every field. -/
theorem componentBasic_iff_matrix {C K : Type} [Field K] (R : C → C → Bool) :
    ComponentBasic R ↔ FieldBasicZeroOneComponent (fun i j => if R i j then (1 : K) else 0) := by
  have hone (b : Bool) : (if b then (1 : K) else 0) = 1 ↔ b = true := by cases b <;> simp
  have hzero (b : Bool) : (if b then (1 : K) else 0) = 0 ↔ b = false := by cases b <;> simp
  have hside (b s t : Bool) :
      (if b then (1 : K) else 0) = (if s = t then 0 else 1) ↔
        b = decide (s ≠ t) := by cases b <;> cases s <;> cases t <;> simp
  have hz : ((fun i j => if R i j then (1 : K) else 0) : Matrix C C K) = 0 ↔
      ∀ i j, R i j = false := by
    simp only [funext_iff, Pi.zero_apply, hzero]
  simp only [ComponentBasic, FieldBasicZeroOneComponent, hone, hside, hz]

namespace Target
variable {q : ℕ} (H : Target q)

def matrix (K : Type*) [Zero K] [One K] : Matrix (Fin q) (Fin q) K :=
  fun i j => if H.adjacent i j then 1 else 0

theorem matrix_symmetric (K : Type*) [Zero K] [One K] :
    ∀ i j, H.matrix K i j = H.matrix K j i := by
  intro i j
  simp only [matrix, H.symmetric i j]

/-- Connectivity forgets loops, while each component retains all its loops. -/
def support : SimpleGraph (Fin q) :=
  RootedRestriction.colorSupport (H.matrix ℝ) (H.matrix_symmetric ℝ)

def Basic : Prop := ∀ c : H.support.ConnectedComponent,
  ComponentBasic (fun i j : c.supp => H.adjacent i.val j.val)

theorem matrix_support_eq (K : Type) [Field K] :
    RootedRestriction.colorSupport (H.matrix K) (H.matrix_symmetric K) = H.support := by
  ext i j
  simp [support, RootedRestriction.colorSupport, matrix]

/-- No algorithm, source-field witness, classification oracle, or target
nonemptiness is supplied when passing to the algebraic source theorem. -/
def language : RealLanguage q 1 0 where
  matrices := fun _ => H.matrix ℝ
  unaries := Fin.elim0
  weights := fun _ => 1
  matrices_algebraic := by
    intro l i j
    dsimp [matrix]
    split <;> first | exact isAlgebraic_one | exact isAlgebraic_zero
  unaries_algebraic := fun l => l.elim0
  weights_algebraic := fun _ => isAlgebraic_one

theorem matrix_zero_one : ∀ i j, H.matrix ℝ i j = 0 ∨ H.matrix ℝ i j = 1 := by
  intro i j
  simp only [matrix]
  split <;> simp

theorem realRelation_eq : ZeroOneMixedMembership.realRelation H.language = H.adjacent := by
  funext i j
  by_cases h : H.adjacent i j = true <;>
    simp [ZeroOneMixedMembership.realRelation, language, matrix, h]

theorem basic_iff_source : H.Basic ↔
    H.language.BasicZeroOneSupport (H.matrix_symmetric ℝ) := by
  constructor <;> intro h c
  · exact (componentBasic_iff_matrix _).mp (h c)
  · exact (componentBasic_iff_matrix _).mpr (h c)

/-- Every component's graph form supplies its literal matrix form in the
actual field used by the unrestricted algorithm. -/
theorem basic_matrix_components (K : Type) [Field K] (h : H.Basic) :
    ∀ c : (RootedRestriction.colorSupport (H.matrix K) (H.matrix_symmetric K)).ConnectedComponent,
      FieldBasicZeroOneComponent (fun i j : c.supp => H.matrix K i.val j.val) := by
  rw [H.matrix_support_eq K]
  intro c
  exact (componentBasic_iff_matrix _).mp (h c)

def planarProblem : PromiseProblem := ZeroOneSharpPMembership.planarProblem q H.adjacent

def generalProblem : PromiseProblem := unrestrictedProblem q H.adjacent

/-- The unrestricted machine uses a fixed rational field presentation and
ends in the very same binary natural-number output codec as the hard branch. -/
theorem general_inFP (h : H.Basic) : H.generalProblem.InFP := by
  let basis : Module.Basis (Fin 1) ℚ ℚ := Module.Basis.singleton (Fin 1) ℚ
  apply unrestricted_inFP_of_valid_mixed basis q H.adjacent
  exact support_valid_fp basis (H.matrix ℚ) (H.matrix_symmetric ℚ) (fun _ => 1)
    (H.basic_matrix_components ℚ h)

theorem planar_inFP (h : H.Basic) : H.planarProblem.InFP :=
  planar_inFP_of_unrestricted q H.adjacent (H.general_inFP h)

/-- The source Potts foundation, full zero--one classification and the charged
natural-answer adapter are all proved imports, not premises of this endpoint. -/
theorem planar_hard (h : ¬H.Basic) : PromisedSharpPHard H.planarProblem := by
  have hh := RealLanguage.theorem71_natural_hard H.language (fun _ => rfl)
    (H.matrix_symmetric ℝ) H.matrix_zero_one (fun hb => h (H.basic_iff_source.mpr hb))
  rw [H.realRelation_eq] at hh
  exact hh

theorem general_hard (h : ¬H.Basic) : PromisedSharpPHard H.generalProblem :=
  unrestricted_hard_of_planar q H.adjacent (H.planar_hard h)

/-- Exact homomorphism cardinality on all valid decoded inputs, including
loops, repeated input edges, disconnected graphs, isolates and empty graphs. -/
theorem general_value_decode (raw : Bits) (g : GraphCode)
    (hd : GraphCode.encoding.decode raw = some g) (hg : g.Valid) :
    H.generalProblem.value raw = BitEncoding.nat.encode
      (ZeroOneSharpPMembership.count q H.adjacent g hg) :=
  congrArg BitEncoding.nat.encode (ZeroOneSharpPMembership.totalCount_decode q H.adjacent raw g hd hg)

end Target

/-- Corollary 12.1, in both input regimes and with genuine #P completeness.
The common structural list is explicit, and the hard side is unconditional. -/
theorem corollary121 {q : ℕ} (H : Target q) :
    (H.Basic → H.planarProblem.InFP ∧ H.generalProblem.InFP) ∧
    (¬H.Basic → CountingComplete H.planarProblem ∧ CountingComplete H.generalProblem) := by
  refine ⟨fun h => ⟨H.planar_inFP h, H.general_inFP h⟩, fun h => ?_⟩
  exact ⟨⟨planar_membership q H.adjacent, H.planar_hard h⟩,
    ⟨unrestricted_membership q H.adjacent, H.general_hard h⟩⟩

end PlanarHom.TargetGraphDichotomy
