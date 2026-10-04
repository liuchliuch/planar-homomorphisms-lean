import PlanarHom.RoutingCellPorts

/-! Exact ordered frontiers of the literal source-routing cells. These lists
retain variable names and geometric column/row positions, including repeated
source literals after their fresh occurrence ports have been materialized. -/
namespace PlanarHom.PositiveBlockProgram

 def CellShape.leftPorts : (s : CellShape) → List (Fin s.portCount)
  | .wireTop | .wireBottom | .wireDown => [⟨0,by decide⟩]
  | .cross => [⟨1,by decide⟩,⟨0,by decide⟩]
  | .fan => [⟨0,by decide⟩]
  | .test => [⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩]

 def CellShape.rightPorts : (s : CellShape) → List (Fin s.portCount)
  | .wireTop | .wireBottom | .wireDown => [⟨1,by decide⟩]
  | .cross => [⟨2,by decide⟩,⟨3,by decide⟩]
  | .fan => [⟨2,by decide⟩,⟨1,by decide⟩]
  | .test => []

 def Cell.leftFrontier (c : Cell) : List PortData := c.shape.leftPorts.map c.portData
 def Cell.rightFrontier (c : Cell) : List PortData := c.shape.rightPorts.map c.portData
 def leftFrontier (cs : List Cell) : List PortData := cs.flatMap Cell.leftFrontier
 def rightFrontier (cs : List Cell) : List PortData := cs.flatMap Cell.rightFrontier

 @[simp] theorem leftFrontier_nil : leftFrontier []=[] := rfl
 @[simp] theorem rightFrontier_nil : rightFrontier []=[] := rfl
 @[simp] theorem leftFrontier_cons (c : Cell) (cs : List Cell) :
    leftFrontier (c::cs)=c.leftFrontier++leftFrontier cs := rfl
 @[simp] theorem rightFrontier_cons (c : Cell) (cs : List Cell) :
    rightFrontier (c::cs)=c.rightFrontier++rightFrontier cs := rfl

 def railFrontier (col : ℕ) : ℕ → List ℕ → List PortData
  | _,[] => []
  | row,x::xs => (x,col,row)::railFrontier col (row+1) xs

 theorem rightFrontier_names (c : Cell) : c.rightFrontier.map Prod.fst=c.outputRefs := by
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> simp [Cell.rightFrontier,CellShape.rightPorts,Cell.portData,Cell.outputRefs]

 theorem wireCells_leftFrontier (shape : CellShape) (hs : shape.kind=.wire)
    (col row m : ℕ) (rs : List ℕ) :
    leftFrontier (wireCells shape col row m rs)=
      railFrontier col (row+if shape=.wireBottom then 1 else 0) rs := by
  induction rs generalizing row m with
  | nil => rfl
  | cons a rs ih =>
    cases shape <;> simp [CellShape.kind] at hs
    all_goals simp [wireCells,leftFrontier_cons,Cell.leftFrontier,CellShape.leftPorts,Cell.portData,
      railFrontier,ih,Nat.add_assoc]

 theorem wireCells_rightFrontier (shape : CellShape) (hs : shape.kind=.wire)
    (col row m : ℕ) (rs : List ℕ) :
    rightFrontier (wireCells shape col row m rs)=
      railFrontier (col+1) (row+if shape=.wireBottom ∨ shape=.wireDown then 1 else 0) (wireRails m rs) := by
  induction rs generalizing row m with
  | nil => rfl
  | cons a rs ih =>
    cases shape <;> simp [CellShape.kind] at hs
    all_goals simp [wireCells,rightFrontier_cons,Cell.rightFrontier,CellShape.rightPorts,Cell.portData,
      railFrontier,wireRails,ih,Nat.add_assoc]

 theorem swapCells_leftFrontier (col row m i : ℕ) (rs : List ℕ) :
    leftFrontier (swapCells col row m i rs)=railFrontier col row rs := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      cases rs with
      | nil => simpa using wireCells_leftFrontier .wireTop rfl col row m [a]
      | cons b rs =>
        simp [swapCells,leftFrontier_cons,Cell.leftFrontier,CellShape.leftPorts,Cell.portData,
          railFrontier,wireCells_leftFrontier,CellShape.kind,Nat.add_assoc]
  | succ i ih =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      simp [swapCells,leftFrontier_cons,Cell.leftFrontier,CellShape.leftPorts,Cell.portData,railFrontier,ih]

 theorem swapCells_rightFrontier (col row m i : ℕ) (rs : List ℕ) :
    rightFrontier (swapCells col row m i rs)=railFrontier (col+1) row (swapLayer m i rs).rails := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      cases rs with
      | nil => simpa [swapCells,swapLayer,passive] using wireCells_rightFrontier .wireTop rfl col row m [a]
      | cons b rs =>
        simp [swapCells,swapLayer,passive,rightFrontier_cons,Cell.rightFrontier,CellShape.rightPorts,Cell.portData,
          railFrontier,wireCells_rightFrontier,CellShape.kind,Nat.add_assoc]
  | succ i ih =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      simp [swapCells,swapLayer,rightFrontier_cons,Cell.rightFrontier,CellShape.rightPorts,Cell.portData,railFrontier,ih]

 theorem copyCells_leftFrontier (col row m i : ℕ) (rs : List ℕ) :
    leftFrontier (copyCells col row m i rs)=railFrontier col row rs := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      simp [copyCells,leftFrontier_cons,Cell.leftFrontier,CellShape.leftPorts,Cell.portData,
        railFrontier,wireCells_leftFrontier,CellShape.kind,Nat.add_assoc]
  | succ i ih =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      simp [copyCells,leftFrontier_cons,Cell.leftFrontier,CellShape.leftPorts,Cell.portData,railFrontier,ih]

 theorem copyCells_rightFrontier (col row m i : ℕ) (rs : List ℕ) :
    rightFrontier (copyCells col row m i rs)=railFrontier (col+1) row (copyLayer m i rs).rails := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      simp [copyCells,copyLayer,passive,rightFrontier_cons,Cell.rightFrontier,CellShape.rightPorts,Cell.portData,
        railFrontier,wireCells_rightFrontier,CellShape.kind,Nat.add_assoc]
  | succ i ih =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      simp [copyCells,copyLayer,rightFrontier_cons,Cell.rightFrontier,CellShape.rightPorts,Cell.portData,railFrontier,ih]
end PlanarHom.PositiveBlockProgram
