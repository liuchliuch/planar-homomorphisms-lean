import PlanarHom.PottsCanvasRecoveryMachines
import PlanarHom.PottsSourceQueryCorrectness
import PlanarHom.PositivePottsProblemBridge
import PlanarHom.ColoringEmitterCounting
import PlanarHom.ColoringEmitterRowTables
import PlanarHom.SourceSimulationOutputBounds

/-! NEW final nonadaptive source reduction, with its one exact outstanding
geometric construction exposed. All query, interpolation, bit-code and count
recovery programs are actual proved FP machines. SourceCanvasCompatible must
be supplied by the ongoing actual canvas/parallel drawing and Euler join; it
is not asserted here and no unconditional Potts foundation is claimed. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.PottsCanvasSourceReduction
open Complexity ParsimoniousNorOneInThree ProperColoringPottsReduction
open PottsSourceCoefficientQueries PottsSourceInverseRows PottsCoefficientPrograms

/-- The precise remaining geometry obligation. The same emitted rows are
used by the runtime serializer, the clockwise drawing and the full Euler law. -/
def SourceCanvasCompatible : Prop :=
  ∀f : NumericFormula,NumericValid f → f.2≠[] → ∀t : ℕ,0<t →
    Nonempty (CompatibleRows ((ColoringEmitter.compile f).parallelLabel 0 t)
      (MixedCode.parallelLabel_valid 0 t 1 0 _ (ColoringEmitter.compile_valid f))
      (parallelRows t (ColoringEmitterRows.compileRows f)))

def data (f : NumericFormula) : Data := (ColoringEmitter.compile f,ColoringEmitterRows.compileRows f)

def prepare (f : NumericFormula) : NumericFormula×List (ℕ×MixedCode) :=
  (f,PottsSourceCoefficientQueries.queries (data f))

theorem fp_prepare : FP formulaEncoding (formulaEncoding.prod queryCode.list) prepare :=
  (fp_id formulaEncoding).pair (((ColoringEmitter.fp_compile.pair ColoringEmitterRows.fp_compileRows).comp
    PottsSourceCoefficientQueries.fp_queries))

theorem queries_members (d : Data) (p : ℕ×MixedCode)
    (hp : p∈PottsSourceCoefficientQueries.queries d) :
    ∃k,k<d.1.vertices ∧ ∃l,l<width d ∧ p=sample d (k+1) (l+1) := by
  obtain ⟨i,hi,hp⟩ := List.mem_map.mp hp
  have hi' : i<d.1.vertices*width d := List.mem_range.mp hi
  have hw : 0<width d := by simp [width]
  have hk : i/width d<d.1.vertices := (Nat.div_lt_iff_lt_mul hw).mpr hi'
  have hl : i%width d<width d := Nat.mod_lt _ hw
  refine ⟨i/width d,hk,i%width d,hl,?_⟩
  have he : (i/width d)*width d+i%width d=i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i (width d)
  calc
    p = indexedSample d i := hp.symm
    _ = indexedSample d ((i/width d)*width d+i%width d) := congrArg (indexedSample d) he.symm
    _ = _ := indexedSample_row_major d _ _ hk hl

theorem nonempty_of_vertex (f : NumericFormula) (k : ℕ)
    (hk : k<(ColoringEmitter.compile f).vertices) : f.2≠[] := by
  intro he
  have hz : (ColoringEmitter.compile f).vertices=0 := by simp [ColoringEmitter.compile,he]
  omega

theorem sample_planar (hc : SourceCanvasCompatible) (f : NumericFormula) (hf : NumericValid f)
    (k l : ℕ) (hk : k<(ColoringEmitter.compile f).vertices) :
    (sample (data f) (k+1) (l+1)).2.PlanarValid 1 0 := by
  obtain ⟨h⟩ := hc f hf (nonempty_of_vertex f k hk) (l+1) (by omega)
  exact serialized_query_planar _ _ _ h (k+1)

theorem sample_value (hc : SourceCanvasCompatible) (f : NumericFormula) (hf : NumericValid f)
    (q : ℕ) (hq : 3≤q) (k l : ℕ) (hk : k<(ColoringEmitter.compile f).vertices) :
    coefficientValue q (sample (data f) (k+1) (l+1))=
      PottsTwoStageInterpolation.radialValue
        (((ColoringEmitter.compile f).parallelLabel 0 (l+1)).toMultiGraph
          (MixedCode.parallelLabel_valid 0 (l+1) 1 0 _ (ColoringEmitter.compile_valid f)))
        ((q:ℚ)-1) (k+1) := by
  obtain ⟨h⟩ := hc f hf (nonempty_of_vertex f k hk) (l+1) (by omega)
  exact serialized_coefficient_value _ _ _ h q (k+1) (by omega) (by omega)

theorem recover_correct (hc : SourceCanvasCompatible) (q : ℕ) (hq : 3≤q)
    (f : NumericFormula) (hf : NumericValid f) :
    PottsCanvasRecovery.recover q
      (f,(PottsSourceCoefficientQueries.queries (data f)).map (coefficientValue q))=
      CountingPositiveOneInThree.count f := by
  let g:=ColoringEmitter.compile f
  have hδ : 1<(q:ℚ)-1 := by
    have hqR : (3:ℚ)≤q := by exact_mod_cast hq
    linarith
  have hg : g.Valid 1 0 := ColoringEmitter.compile_valid f
  have hcount := PottsTwoStageMachines.recoverThreeColoring_count g (ColoringEmitter.compile_valid f)
    ((q:ℚ)-1) hδ ((PottsSourceCoefficientQueries.queries (data f)).map (coefficientValue q))
  have hcvalue : PottsTwoStageMachines.recoverThreeColoring ((q:ℚ)-1)
      (g.vertices,(g.edges.length,(PottsSourceCoefficientQueries.queries (data f)).map (coefficientValue q)))=
      (totalColorings 3 g:ℚ) := by
    apply (hcount ?_).trans
    · simp only [totalColorings,dif_pos hg]
    · intro k hk l hl
      exact (getD_answers_row_major (data f) (coefficientValue q) k l hk hl).trans
        (sample_value hc f hf q hq k l hk)
  rw [PottsCanvasRecovery.recover_of_coloring_value q f _ hcvalue]
  exact ColoringEmitter.recover_correct f hf

def reduction (hc : SourceCanvasCompatible) (q : ℕ) (hq : 3≤q) :
    PromisePolyTimeTuringReduction CountingPositiveOneInThree.problem (PottsCoefficientReduction.problem q) := by
  let coeffRed:=PositivePottsProblemBridge.coefficient_reduction q (by omega)
  let view : ∀raw,CountingPositiveOneInThree.problem.valid raw → NumericFormula := fun _ h=>Classical.choose h
  have same : ∀raw h,formulaEncoding.encode (view raw h)=raw := fun _ h=>(Classical.choose_spec h).2
  have hv : ∀raw h,NumericValid (view raw h) := fun _ h=>(Classical.choose_spec h).1
  apply nonadaptiveReduction (p:=coeffRed.outputPolynomial)
    formulaEncoding formulaEncoding queryCode fieldCode BitEncoding.nat
    CountingPositiveOneInThree.problem (PottsCoefficientReduction.problem q)
    prepare (coefficientValue q) (PottsCanvasRecovery.recover q)
    (Classical.choice fp_prepare) (Classical.choice (PottsCanvasRecovery.fp_recover q)) view same
  · intro raw h p hp
    obtain ⟨k,hk,l,hl,rfl⟩ := queries_members (data (view raw h)) p hp
    exact coefficient_problem_valid q _ (sample_planar hc _ (hv raw h) k l hk)
  · intro p _
    exact coefficient_problem_value q p
  · intro raw h
    change BitEncoding.nat.encode (PottsCanvasRecovery.recover q
      (view raw h,(PottsSourceCoefficientQueries.queries (data (view raw h))).map (coefficientValue q)))=_
    rw [recover_correct hc q hq _ (hv raw h)]
    change _=encodedFunction formulaEncoding BitEncoding.nat CountingPositiveOneInThree.count [] raw
    conv_rhs => rw [←same raw h,encodedFunction_encode]
  · exact coeffRed.output_length_bound

/-- Genuine hardness follows once the actual source geometry join is supplied;
there is no extra seed, FP or field-code assumption. -/
theorem positivePottsFoundation_of_canvas (hc : SourceCanvasCompatible) :
    AlgebraicProductInterpolation.RealLanguage.PositivePottsFoundation := by
  intro q hq
  exact CountingPositiveOneInThree.promisedSharpPHard.trans
    ((reduction hc q hq).trans (PositivePottsProblemBridge.coefficient_reduction q (by omega)))

end PlanarHom.PottsCanvasSourceReduction
