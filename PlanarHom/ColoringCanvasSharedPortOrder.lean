import PlanarHom.ColoringCanvasBandOrder
import PlanarHom.ColoringEmitterCanvas

/-! Two distinct actual cells can share a signal only across one successive
column boundary. The later cell contributes the rightward germ block, before
the earlier cell's leftward block in the clockwise-from-up order. -/
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree

theorem Cell.left_port_rows (c : Cell) (p : Fin c.shape.portCount)
    (hx : (c.portData p).2.1=c.column) :
    c.row+c.shape.leftLo≤(c.portData p).2.2 ∧ (c.portData p).2.2≤c.row+c.shape.leftHi := by
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> fin_cases p
  all_goals simp [Cell.portData,CellShape.leftLo,CellShape.leftHi] at hx ⊢
  all_goals omega

theorem Cell.right_port_rows (c : Cell) (p : Fin c.shape.portCount)
    (hx : (c.portData p).2.1=c.column+1) :
    c.row+c.shape.rightLo≤(c.portData p).2.2 ∧ (c.portData p).2.2≤c.row+c.shape.rightHi := by
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> fin_cases p
  all_goals simp [Cell.portData,CellShape.rightLo,CellShape.rightHi] at hx ⊢
  all_goals omega

theorem Cell.shared_port_order (c d : Cell) (p : Fin c.shape.portCount) (q : Fin d.shape.portCount)
    (horder : c.ColorBandBefore d) (hshare : (c.portData p).2=(d.portData q).2) :
    d.column=c.column+1 ∧ (c.portData p).2.1=c.column+1 ∧ (d.portData q).2.1=d.column := by
  have hx:=congrArg Prod.fst hshare
  have hy:=congrArg Prod.snd hshare
  have hc:=(c.port_bounds p).1
  have hd:=(d.port_bounds q).1
  rcases horder with hcol | ⟨hcol,hl,hr⟩
  · omega
  · exfalso
    rcases hc with hc | hc
    · have hd' : (d.portData q).2.1=d.column := by omega
      have hcp:=c.left_port_rows p hc
      have hdp:=d.left_port_rows q hd'
      omega
    · have hd' : (d.portData q).2.1=d.column+1 := by omega
      have hcp:=c.right_port_rows p hc
      have hdp:=d.right_port_rows q hd'
      omega

theorem canvas_shared_port_order (f : NumericFormula) (i j : CanvasIndex f) (hij : i<j)
    (p : Fin (canvasCell f i).shape.portCount) (q : Fin (canvasCell f j).shape.portCount)
    (hshare : boundaryPort f i p=boundaryPort f j q) :
    (canvasCell f j).column=(canvasCell f i).column+1 ∧
    ((canvasCell f i).portData p).2.1=(canvasCell f i).column+1 ∧
    ((canvasCell f j).portData q).2.1=(canvasCell f j).column :=
  Cell.shared_port_order _ _ p q ((List.pairwise_iff_get.mp (canvas_colorBand_ordered f)) i j hij)
    (congrArg Subtype.val hshare)

end PlanarHom.PositiveBlockProgram
