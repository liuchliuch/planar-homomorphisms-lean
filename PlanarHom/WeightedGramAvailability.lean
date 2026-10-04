import PlanarHom.UniformWeightedChainSimulation
import PlanarHom.MixedParallelMachines
import PlanarHom.PlanarRibbonExistence

/-! A genuine weighted two-edge/parallel gadget provides the Gram core without
introducing an assumed gadget-computability rule. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.PositiveWeightRemoval
open Complexity Complexity.MixedCode FiniteLanguageAliases PairProjectionMachines
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K] [DecidableEq C]
variable {dimension bt ut : ℕ}

def gramCoreField (B : Matrix C C K) (w : C → K) (p : ℕ) : Matrix C C K :=
  fun i j => ((B * Matrix.diagonal w * B) i j)^p

def gramTransform (bt selected p : ℕ) (g : MixedCode) : MixedCode :=
  (g.parallelLabel bt p).stretchLabelLength bt selected 2

theorem gramTransform_planar (g : MixedCode) (hg : g.PlanarValid (bt+1) ut)
    (selected : Fin bt) (p : ℕ) : (gramTransform bt selected.val p g).PlanarValid bt ut :=
  (g.parallelLabel bt p).stretchLabelLength_planar (hg.parallelLabel bt p) bt 2 selected
    ((g.parallelLabel bt p).appended_companion_bound (hg.parallelLabel bt p).1)

theorem powered_appendOne (M : Fin bt → Matrix C C K) (N : Matrix C C K) (p : ℕ) :
    (fun l : Fin (bt+1) => fun i j => if l.val=bt then (appendOne M N l i j)^p else appendOne M N l i j) =
      appendOne M (fun i j=>N i j^p) := by
  funext l
  refine Fin.lastCases ?_ (fun k=>?_) l
  · simp [appendOne_aux]
  · change (fun i j=>if (Fin.castAdd 1 k).val=bt then
      (appendOne M N (Fin.castAdd 1 k) i j)^p else appendOne M N (Fin.castAdd 1 k) i j) =
      appendOne M (fun i j=>N i j^p) (Fin.castAdd 1 k)
    simp [k.isLt.ne,appendOne_old]

theorem gramTransform_evaluate (g : MixedCode) (hg : g.Valid (bt+1) ut)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K) (old : Fin bt) (p : ℕ) :
    totalEvaluation M U w (gramTransform bt old.val p g) =
      g.evaluate hg (appendOne M (gramCoreField (M old) w p)) U w := by
  have hv := parallelLabel_valid bt p (bt+1) ut g hg
  have ht := (g.parallelLabel bt p).stretchLabelLength_valid hv bt 2 old
    ((g.parallelLabel bt p).appended_companion_bound hv)
  unfold gramTransform
  rw [totalEvaluation_valid _ _ _ _ ht,
    evaluate_stretchLabelLength_weighted _ hv old 2 M U w,
    evaluate_parallelLabel _ hg bt p _ U w,powered_appendOne]
  congr 2
  ext i j
  simp [gramCoreField,weightedChain,Matrix.mul_assoc]

theorem fp_gramTransform (selected p : ℕ) :
    FP MixedCode.encoding MixedCode.encoding (gramTransform bt selected p) := by
  have hparallel := ((fp_const MixedCode.encoding BitEncoding.unaryNat p).pair (fp_id MixedCode.encoding)).comp
    (MixedParallelMachines.fp_parallelLabel bt)
  exact ((fp_const MixedCode.encoding BitEncoding.unaryNat 2).pair hparallel).comp
    (fp_stretchLabelLength bt selected)

/-- Actual joint availability of every fixed weighted Gram entrywise power. -/
def gramAppendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K) (old : Fin bt) (p : ℕ) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (gramCoreField (M old) w p)) U w)
      (evaluationProblem basis M U w) := by
  apply planarReductionOfPipeline basis BitEncoding.bits
    (appendOne M (gramCoreField (M old) w p)) U w M U w
    (fun g => ([],[gramTransform bt old.val p g])) (fun p : Bits × List K => p.2.sum)
  · have ht := fp_gramTransform (bt:=bt) old.val p
    have hl := (ht.pair (fp_const MixedCode.encoding MixedCode.encoding.list [])).comp
      (ListMutationMachines.fp_cons MixedCode.encoding)
    exact (fp_const MixedCode.encoding BitEncoding.bits []).pair hl
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    have he : query=gramTransform bt old.val p g := List.mem_singleton.mp hq
    subst query
    exact gramTransform_planar g hg old p
  · intro g hg
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
      gramTransform_evaluate g hg.1 M U w old p

end PlanarHom.PositiveWeightRemoval
