import PlanarHom.ColoringEmitterRowRealization
import PlanarHom.ColoringEmitterMacroRows

/-! NEW actual geometric macro-row realization by the executable source-only
row compiler. No local row table or ordering witness is supplied by the caller. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph PositiveBlockProgram ParsimoniousNorOneInThree PlanarityLRRealization

 def geometricRows (f : NumericFormula) : RotationRows (graph f) :=
   rowsFrom f (fun i=>MacroRows.localRows (canvasCell f i).shape)

 theorem macroTable_get (s : CellShape) (w : LocalPatch.NumericVertex s) :
     (ColoringEmitterRows.macroTable s.kind)[w.val]?.getD []=MacroRows.raw s w := by
   cases s
   all_goals
     have hw:=w.isLt
     simp only [CellShape.kind,Macro.vertexCount] at hw
     simp only [ColoringEmitterRows.macroTable,CellShape.kind,MacroRows.raw,
       List.getElem?_ofFn,hw,dif_pos,Option.getD_some]
     rfl

 theorem macroRowLaw (f : NumericFormula) :
     LocalRowLaw f (fun i=>MacroRows.localRows (canvasCell f i).shape) ColoringEmitterRows.macroTable := by
   intro i w
   rw [macroTable_get]
   exact MacroRows.localRows_erase _ w

 def computedGeometricRows (f : NumericFormula) (hf:NumericValid f) (hne:f.2≠[]) :
     RotationRows ((compile f).toMultiGraph (compile_valid f)) :=
   (geometricRows f).transport (compile_incidenceEquiv f hf hne)

 theorem compileRows_get (f : NumericFormula) (hf:NumericValid f) (hne:f.2≠[])
     (v : Fin (compile f).vertices) :
     (ColoringEmitterRows.compileRows f).getD v.val []=
       ((computedGeometricRows f hf hne).row v).map eraseDart :=
   rows_getD_eq f hf hne _ _ (macroRowLaw f) v

end PlanarHom.ColoringEmitter.Canvas
