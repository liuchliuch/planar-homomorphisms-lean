import PlanarHom.ColoringEmitterCanvas

/-! NEW every retained registry signal is an actual cell port on a nonempty
source canvas. This is proved from the literal routing stage construction. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree

theorem Cell.portCount_pos (c : Cell) : 0<c.shape.portCount := by cases c.shape <;> decide

theorem Cell.port_zero_name (c : Cell) :
    (c.portData ⟨0,c.portCount_pos⟩).1=c.args.1 := by
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> rfl

theorem wireCells_inputs_cover (shape : CellShape) (col row m : ℕ) (rs : List ℕ)
    (x : ℕ) (hx:x∈rs) :
    ∃c∈wireCells shape col row m rs,∃p:Fin c.shape.portCount,(c.portData p).1=x := by
  induction rs generalizing row m with
  | nil => simp at hx
  | cons a rs ih =>
    rcases List.mem_cons.mp hx with rfl|hx
    · let c : Cell:=⟨col,row,shape,m,(x,0,0)⟩
      exact ⟨c,by simp [wireCells,c],⟨0,c.portCount_pos⟩,c.port_zero_name⟩
    · obtain ⟨c,hc,p,hp⟩:=ih (row+1) (m+6) hx
      exact ⟨c,List.mem_cons_of_mem _ hc,p,hp⟩

theorem swapCells_inputs_cover (col row m i : ℕ) (rs : List ℕ) (x : ℕ) (hx:x∈rs) :
    ∃c∈swapCells col row m i rs,∃p:Fin c.shape.portCount,(c.portData p).1=x := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => simp at hx
    | cons a rs =>
      cases rs with
      | nil => exact wireCells_inputs_cover .wireTop col row m [a] x hx
      | cons b rs =>
        rcases List.mem_cons.mp hx with rfl|hx
        · exact ⟨⟨col,row,.cross,m,(b,x,0)⟩,by simp [swapCells],(1:Fin 4),rfl⟩
        rcases List.mem_cons.mp hx with rfl|hx
        · exact ⟨⟨col,row,.cross,m,(x,a,0)⟩,by simp [swapCells],(0:Fin 4),rfl⟩
        · obtain ⟨c,hc,p,hp⟩:=wireCells_inputs_cover .wireBottom col (row+1) (m+15) rs x hx
          exact ⟨c,List.mem_cons_of_mem _ hc,p,hp⟩
  | succ i ih =>
    cases rs with
    | nil => simp at hx
    | cons a rs =>
      rcases List.mem_cons.mp hx with rfl|hx
      · exact ⟨⟨col,row,.wireTop,m,(x,0,0)⟩,by simp [swapCells],(0:Fin 2),rfl⟩
      · obtain ⟨c,hc,p,hp⟩:=ih (row+1) (m+6) rs hx
        exact ⟨c,List.mem_cons_of_mem _ hc,p,hp⟩

theorem copyCells_inputs_cover (col row m i : ℕ) (rs : List ℕ) (x : ℕ) (hx:x∈rs) :
    ∃c∈copyCells col row m i rs,∃p:Fin c.shape.portCount,(c.portData p).1=x := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => simp at hx
    | cons a rs =>
      rcases List.mem_cons.mp hx with rfl|hx
      · exact ⟨⟨col,row,.fan,m,(x,0,0)⟩,by simp [copyCells],(0:Fin 3),rfl⟩
      · obtain ⟨c,hc,p,hp⟩:=wireCells_inputs_cover .wireDown col (row+1) (m+12) rs x hx
        exact ⟨c,List.mem_cons_of_mem _ hc,p,hp⟩
  | succ i ih =>
    cases rs with
    | nil => simp at hx
    | cons a rs =>
      rcases List.mem_cons.mp hx with rfl|hx
      · exact ⟨⟨col,row,.wireTop,m,(x,0,0)⟩,by simp [copyCells],(0:Fin 2),rfl⟩
      · obtain ⟨c,hc,p,hp⟩:=ih (row+1) (m+6) rs hx
        exact ⟨c,List.mem_cons_of_mem _ hc,p,hp⟩

theorem checkCells_inputs_cover (col n m : ℕ) (rs : List ℕ) (hlen:rs.length=n+3)
    (x : ℕ) (hx:x∈rs) :
    ∃c∈checkCells col n m rs,∃p:Fin c.shape.portCount,(c.portData p).1=x := by
  obtain ⟨j,hj,hx⟩:=List.mem_iff_getElem.mp hx
  by_cases hjn:j<n
  · have hjt:j<(rs.take n).length := by simp; omega
    have hm := List.getElem_mem hjt
    rw [List.getElem_take] at hm
    rw [hx] at hm
    obtain ⟨c,hc,p,hp⟩:=wireCells_inputs_cover .wireTop col 0 m (rs.take n) x hm
    exact ⟨c,List.mem_append_left _ hc,p,hp⟩
  · have hjn' : j=n ∨ j=n+1 ∨ j=n+2 := by omega
    let c : Cell:=⟨col,n,.test,m+6*(rs.take n).length,(getRef rs n,getRef rs (n+1),getRef rs (n+2))⟩
    have hc:c∈checkCells col n m rs := by simp [checkCells,c]
    rcases hjn' with rfl|rfl|rfl
    · refine ⟨c,hc,(0:Fin 3),?_⟩
      simpa [c,Cell.portData,getRef,hj] using hx
    · refine ⟨c,hc,(1:Fin 3),?_⟩
      simpa [c,Cell.portData,getRef,hj] using hx
    · refine ⟨c,hc,(2:Fin 3),?_⟩
      simpa [c,Cell.portData,getRef,hj] using hx

theorem Stage.cells_inputs_cover (s : Stage) (col m : ℕ) (rs : List ℕ)
    (hs:s.Admissible rs) (x : ℕ) (hx:x∈rs) :
    ∃c∈s.cells col m rs,∃p:Fin c.shape.portCount,(c.portData p).1=x := by
  cases s with
  | swap i => exact swapCells_inputs_cover col 0 m i rs x hx
  | copy i => exact copyCells_inputs_cover col 0 m i rs x hx
  | check n => exact checkCells_inputs_cover col n m rs hs x hx

theorem canvas_initial_port (f : NumericFormula) (hf:NumericValid f) (hne:f.2≠[])
    (x : Fin f.1) : ∃i:CanvasIndex f,∃p:Fin (canvasCell f i).shape.portCount,
      ((canvasCell f i).portData p).1=x.val := by
  have hs:=formulaStages_admissible f.2 f.1 f.1 (List.range f.1)
    (fun z hz=>List.mem_range.mp hz) (by simp) hf
  have hst : formulaStages f.1 f.2≠[] := by
    cases hfs:f.2 with
    | nil => exact False.elim (hne hfs)
    | cons c cs => simp [formulaStages,hfs,clauseStages]
  obtain ⟨s,ss,hss⟩:=List.exists_cons_of_ne_nil hst
  rw [hss] at hs
  obtain ⟨c,hc,p,hp⟩:=s.cells_inputs_cover 0 f.1 (List.range f.1) hs.1 x.val (List.mem_range.mpr x.isLt)
  have hcanvas:c∈canvas f := by
    unfold canvas
    rw [←stagesCells_formulaStages,hss]
    exact List.mem_append_left _ hc
  obtain ⟨i,hi⟩:=List.mem_iff_get.mp hcanvas
  subst c
  exact ⟨i,p,hp⟩

theorem canvas_boundary_port_coverage (f : NumericFormula) (hf:NumericValid f) (hne:f.2≠[])
    (b : Boundary f) : ∃i:CanvasIndex f,∃p:Fin (canvasCell f i).shape.portCount,
      boundaryPort f i p=b := by
  rcases Finset.mem_union.mp b.property with hb|hb
  · obtain ⟨x,hx,hpos⟩:=Finset.mem_image.mp hb
    obtain ⟨i,p,hp⟩:=canvas_initial_port f hf hne x
    refine ⟨i,p,?_⟩
    apply boundaryName_injective f hf
    rw [boundaryName_port,hp]
    have he : b=initialBoundary f x := Subtype.ext hpos.symm
    rw [he,boundaryName_initial]
  · obtain ⟨i,hi,hport⟩:=Finset.mem_biUnion.mp hb
    obtain ⟨p,hp,hpos⟩:=Finset.mem_image.mp hport
    exact ⟨i,p,Subtype.ext hpos⟩

end PlanarHom.PositiveBlockProgram
