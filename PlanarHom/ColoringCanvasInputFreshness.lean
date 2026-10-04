import PlanarHom.ColoringCanvasConsumption

/-! NEW canonical injective lookup of every consumed registry signal. The
proof is the exact frontier run's single-consumption invariant, so no consumed
input marker can coincide with a different patch attachment marker. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open PositiveBlockProgram ParsimoniousNorOneInThree

 abbrev InputPort (f:NumericFormula) :=
   (i:Index f) × {p:Fin (canvasCell f i).shape.portCount // p∈(canvasCell f i).shape.leftPorts}

 def inputSignal (f:NumericFormula) (a:InputPort f) : Signal f := boundaryPort f a.1 a.2.val

 theorem left_name_mem (c:Cell) (p:Fin c.shape.portCount) (hp:p∈c.shape.leftPorts) :
     (c.portData p).1∈c.leftFrontier.map Prod.fst := by
   simp only [Cell.leftFrontier,List.mem_map]
   exact ⟨c.portData p,⟨p,hp,rfl⟩,rfl⟩

 theorem consumed_blocks_disjoint (f:NumericFormula) (hf:NumericValid f) :
     (canvas f).Pairwise (fun c d=>List.Disjoint (c.leftFrontier.map Prod.fst) (d.leftFrontier.map Prod.fst)) := by
   have h:=canvas_consumed_names_nodup f hf
   simp only [leftFrontier,List.map_flatMap] at h
   exact (List.nodup_flatMap.mp h).2

 theorem inputSignal_injective (f:NumericFormula) (hf:NumericValid f) :
     Function.Injective (inputSignal f) := by
   rintro ⟨i,p⟩ ⟨j,q⟩ he
   have hn:=congrArg (boundaryName f hf) he
   change boundaryName f hf (boundaryPort f i p.val)=boundaryName f hf (boundaryPort f j q.val) at hn
   rw [boundaryName_port,boundaryName_port] at hn
   have hp:=left_name_mem (canvasCell f i) p.val p.property
   have hq:=left_name_mem (canvasCell f j) q.val q.property
   rcases lt_trichotomy i.val j.val with hij|hij|hji
   · have hd:=List.pairwise_iff_get.mp (consumed_blocks_disjoint f hf) i j hij
     exact False.elim (List.disjoint_left.mp hd hp (hn ▸ hq))
   · have hidx:i=j:=Fin.ext hij
     subst j
     have hpos:=congrArg (fun b:Boundary f=>b.val) he
     have hpq:p.val=q.val := (canvasCell f i).port_positions_injective hpos
     have hsub:p=q:=Subtype.ext hpq
     subst q
     rfl
   · have hd:=List.pairwise_iff_get.mp (consumed_blocks_disjoint f hf) j i hji
     exact False.elim (List.disjoint_left.mp hd hq (hn.symm ▸ hp))

end PlanarHom.ColoringEmitter.Canvas
