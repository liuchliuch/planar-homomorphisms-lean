import PlanarHom.PottsSourceCoefficientQueries
import PlanarHom.PottsTwoStageColoringRecovery
import PlanarHom.ColoringEmitterRecoveryMachines
import PlanarHom.ProperColoringNaturalReduction

/-! NEW actual final source recovery. Rational two-stage interpolation is
followed by exact natural extraction and the emitter's component/palette
normalization, retaining its separately proved empty-formula branch. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.PottsCanvasRecovery
open Complexity PairProjectionMachines ParsimoniousNorOneInThree
open PottsCoefficientPrograms ProperColoringPottsReduction
abbrev postCode := formulaEncoding.prod fieldCode.list

def recover (q : ℕ) (p : NumericFormula×List ℚ) : ℕ :=
  let g:=ColoringEmitter.compile p.1
  let colorCount:=PottsTwoStageMachines.recoverThreeColoring ((q:ℚ)-1)
    (g.vertices,(g.edges.length,p.2))
  ColoringEmitter.recover (p.1,[colorCount.num.natAbs])

theorem fp_recover (q : ℕ) : FP postCode BitEncoding.nat (recover q) := by
  have hf:=fp_fst formulaEncoding fieldCode.list
  have ha:=fp_snd formulaEncoding fieldCode.list
  have hg:=hf.comp ColoringEmitter.fp_compile
  have hn:=hg.comp MixedCode.fp_vertices
  have hm:=hg.comp PottsSourceInverseRows.fp_edgeCountUnary
  have hc:=(hn.pair (hm.pair ha)).comp (PottsTwoStageMachines.fp_recoverThreeColoring ((q:ℚ)-1))
  have he:=hc.comp fp_extractNatural
  have hlist:=(he.pair (fp_const postCode BitEncoding.nat.list [])).comp
    (ListMutationMachines.fp_cons BitEncoding.nat)
  exact (hf.pair hlist).comp ColoringEmitter.fp_recover

theorem recover_of_coloring_value (q : ℕ) (f : NumericFormula) (answers : List ℚ)
    (h : PottsTwoStageMachines.recoverThreeColoring ((q:ℚ)-1)
      ((ColoringEmitter.compile f).vertices,((ColoringEmitter.compile f).edges.length,answers))=
      (totalColorings 3 (ColoringEmitter.compile f):ℚ)) :
    recover q (f,answers)=ColoringEmitter.recover (f,[totalColorings 3 (ColoringEmitter.compile f)]) := by
  unfold recover
  dsimp only
  rw [h,extractNatural_natCast]

end PlanarHom.PottsCanvasRecovery
