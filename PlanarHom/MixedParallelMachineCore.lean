import PlanarHom.SelectedLabelOracleMachine
import PlanarHom.RelationalStackTransfer

/-! Actual finite-control selected-label mixed-occurrence transducer. -/

namespace PlanarHom.MixedParallelMachines
open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition

inductive Stack | input | factor | back | vertices | edge | buffer | payload | output | count
  | saved | classifier | unaries
  deriving DecidableEq, Fintype
inductive Label | factor | vertices | outerEdges | saveUnaries | restoreEdges | header | startEdge
  | saveCounter | edge | reverseEdge | prepareClass | tagClass | queryClass | readClass | restoreCounter
  | route | check | emit | restoreEdge | tagInc | queryRepeat | querySingle | restoreFactor
  | clearEdge | nextEdge | reversePayload | frameCount | prefixCount | frameEdges | restoreUnaries
  | prefixEdges | prefixVertices | clearFactor | halt
  deriving DecidableEq, Fintype

structure Data where
  input : Bits := []
  factor : Bits := []
  back : Bits := []
  vertices : Bits := []
  edge : Bits := []
  buffer : Bits := []
  payload : Bits := []
  output : Bits := []
  count : Bits := []
  saved : Bits := []
  classifier : Bits := []
  unaries : Bits := []

def Data.get (d : Data) : Stack → Bits
  | .input => d.input | .factor => d.factor | .back => d.back | .vertices => d.vertices
  | .edge => d.edge | .buffer => d.buffer | .payload => d.payload | .output => d.output
  | .count => d.count | .saved => d.saved | .classifier => d.classifier | .unaries => d.unaries

def Data.set (d : Data) (k : Stack) (xs : Bits) : Data := match k with
  | .input => {d with input:=xs} | .factor => {d with factor:=xs} | .back => {d with back:=xs}
  | .vertices => {d with vertices:=xs} | .edge => {d with edge:=xs} | .buffer => {d with buffer:=xs}
  | .payload => {d with payload:=xs} | .output => {d with output:=xs} | .count => {d with count:=xs}
  | .saved => {d with saved:=xs} | .classifier => {d with classifier:=xs} | .unaries => {d with unaries:=xs}

@[simp] theorem update_get (d : Data) (k : Stack) (xs : Bits) :
    Function.update d.get k xs = (d.set k xs).get := by
  funext j; cases k <;> cases j <;> simp [Data.get,Data.set]

abbrev State := Bool × Option Bool
abbrev Statement := Stmt (fun _ : Stack=>Bool) Label State

def resetGoto (next : Label) : Statement := .load (fun v=>(v.1,none)) (.goto (fun _=>next))

def pushParsed (dest : Option Stack) (framed : Bool) (next : Label) : Statement :=
  match dest with
  | none => resetGoto next
  | some k => if framed then .push k (fun _=>true) (.push k (fun v=>v.2.getD false) (resetGoto next))
    else .push k (fun v=>v.2.getD false) (resetGoto next)

def endParsed (dest : Option Stack) (framed : Bool) (next : Label) : Statement :=
  match dest with
  | none => resetGoto next
  | some k => if framed then .push k (fun _=>false) (resetGoto next) else resetGoto next

def parseStmt (dest : Option Stack) (framed : Bool) (loop next : Label) : Statement :=
  .pop .input (fun v a=>(v.1,a)) (.branch (fun v=>v.2.getD false)
    (.pop .input (fun v a=>(v.1,a)) (pushParsed dest framed loop)) (endParsed dest framed next))

def frameStmt (src : Stack) (loop next : Label) : Statement :=
  .pop src (fun v a=>(v.1,a)) (.branch (fun v=>v.2.isSome)
    (.push .buffer (fun _=>true) (.push .buffer (fun v=>v.2.getD false) (resetGoto loop)))
    (.push .buffer (fun _=>false) (resetGoto next)))

def program : Label → Statement
  | .factor => parseStmt (some .factor) false .factor .vertices
  | .vertices => parseStmt (some .vertices) true .vertices .outerEdges
  | .outerEdges => parseStmt (some .buffer) false .outerEdges .saveUnaries
  | .saveUnaries => transferStmt .input .unaries id id .saveUnaries .restoreEdges
  | .restoreEdges => transferStmt .buffer .input id id .restoreEdges .header
  | .header => parseStmt none false .header .startEdge
  | .startEdge => .peek .input (fun v a=>(v.1,a)) (.branch (fun v=>v.2.isSome)
      (resetGoto .saveCounter) (resetGoto .reversePayload))
  | .saveCounter => transferStmt .count .saved id id .saveCounter .edge
  | .edge => .pop .input (fun v a=>(v.1,a)) (.branch (fun v=>v.2.getD false)
      (.pop .input (fun v a=>(v.1,a)) (.push .buffer (fun _=>true)
        (.push .buffer (fun v=>v.2.getD false) (.push .classifier (fun v=>v.2.getD false) (resetGoto .edge)))))
      (.push .buffer (fun _=>false) (resetGoto .reverseEdge)))
  | .reverseEdge => transferStmt .buffer .edge id id .reverseEdge .prepareClass
  | .prepareClass => transferStmt .classifier .count id id .prepareClass .tagClass
  | .tagClass => .push .count (fun _=>true) (resetGoto .queryClass)
  | .queryClass => .halt
  | .readClass => .pop .count (fun v a=>(v.1,a))
      (.load (fun v=>(v.2.getD false,none)) (.goto (fun _=>.restoreCounter)))
  | .restoreCounter => transferStmt .saved .count id id .restoreCounter .route
  | .route => .branch (fun v=>v.1) (resetGoto .check) (resetGoto .emit)
  | .check => .pop .factor (fun v a=>(v.1,a)) (.branch (fun v=>v.2.isSome)
      (.push .back (fun v=>v.2.getD false) (resetGoto .emit)) (resetGoto .restoreFactor))
  | .emit => transfer₂Stmt .edge .buffer .payload id id id .emit .restoreEdge
  | .restoreEdge => transferStmt .buffer .edge id id .restoreEdge .tagInc
  | .tagInc => .push .count (fun _=>false)
      (.branch (fun v=>v.1) (resetGoto .queryRepeat) (resetGoto .querySingle))
  | .queryRepeat => .halt
  | .querySingle => .halt
  | .restoreFactor => transferStmt .back .factor id id .restoreFactor .clearEdge
  | .clearEdge => clearStmt .edge .clearEdge .nextEdge
  | .nextEdge => .load (fun _=>(false,none)) (.goto (fun _=>.startEdge))
  | .reversePayload => transferStmt .payload .output id id .reversePayload .frameCount
  | .frameCount => frameStmt .count .frameCount .prefixCount
  | .prefixCount => transferStmt .buffer .output id id .prefixCount .frameEdges
  | .frameEdges => frameStmt .output .frameEdges .restoreUnaries
  | .restoreUnaries => transferStmt .unaries .output id id .restoreUnaries .prefixEdges
  | .prefixEdges => transferStmt .buffer .output id id .prefixEdges .prefixVertices
  | .prefixVertices => transferStmt .vertices .output id id .prefixVertices .clearFactor
  | .clearFactor => clearStmt .factor .clearFactor .halt
  | .halt => .load (fun _=>(false,none)) .halt

/-- Fixed caller machine. Only the supplied total classifier/successor oracle
depends on the chosen label; all stacks and finite states are explicitly finite. -/
def machine : OracleTM2 where
  core := {
    tm := { K:=Stack, Γ:=fun _=>Bool, k₀:=.input, k₁:=.output, Λ:=Label, main:=.factor, σ:=State, initialState:=(false,none), Γk₀Fin:=inferInstance, m:=program }
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool }
  finiteAlphabet := fun _=>inferInstance
  queryStack := .count
  answerStack := .count
  queryAlphabet := Equiv.refl Bool
  answerAlphabet := Equiv.refl Bool
  request | .queryClass => some .readClass | .queryRepeat => some .check | .querySingle => some .clearEdge | _ => none

def cfg (l : Label) (flag : Bool) (d : Data) : machine.Cfg := ⟨some l,(flag,none),d.get⟩

def Runs (selected : ℕ) (c d : machine.Cfg) (bound : ℕ) : Prop :=
  ∃ s t qs, machine.Run (selectedOracle selected) c d s t qs ∧ t≤bound

variable (selected : ℕ)

theorem Runs.refl (c : machine.Cfg) : Runs selected c c 0 := ⟨0,0,[],.refl c,by rfl⟩
theorem Runs.trans {selected : ℕ} {c d e : machine.Cfg} {n k : ℕ} (h : Runs selected c d n) (h' : Runs selected d e k) :
    Runs selected c e (n+k) := by
  obtain ⟨s,t,qs,hr,ht⟩ := h; obtain ⟨s',t',qs',hr',ht'⟩ := h'
  exact ⟨_,_,_,hr.trans hr',Nat.add_le_add ht ht'⟩
theorem Runs.mono {selected : ℕ} {c d : machine.Cfg} {n k : ℕ} (h : Runs selected c d n) (hk : n≤k) : Runs selected c d k := by
  obtain ⟨s,t,qs,hr,ht⟩ := h; exact ⟨s,t,qs,hr,ht.trans hk⟩

theorem ordinary {c d : machine.Cfg} (hn : machine.continuation c=none)
    (hs : machine.core.tm.step c=some d) : Runs selected c d 1 :=
  ⟨1,1,[],.ordinary hn hs (.refl d),by rfl⟩

theorem ordinary_label (l : Label) (hn : machine.request l=none) (v : State) (S : Stack→Bits) :
    Runs selected ⟨some l,v,S⟩ (stepAux (program l) v S) 1 := ordinary selected hn rfl

theorem transfer (flag : Bool) (i j : Stack) (hij : i≠j) (loop next : Label)
    (hp : program loop=transferStmt i j id id loop next) (hn : machine.request loop=none) (d : Data) :
    Runs selected (cfg loop flag d) (cfg next flag ((d.set i []).set j ((d.get i).reverse++d.get j))) ((d.get i).length+1) := by
  have h := transfer_rel (Runs selected) (@Runs.trans selected) i j hij id id loop next
    (fun v r S=>by rw [←hp]; exact ordinary_label selected loop hn (v,r) S) flag none d.get
  simpa [cfg,machine,transferStore,Function.comp_def] using h

theorem transfer₂ (flag : Bool) (i j k : Stack) (hij : i≠j) (hik : i≠k) (hjk : j≠k) (loop next : Label)
    (hp : program loop=transfer₂Stmt i j k id id id loop next) (hn : machine.request loop=none) (d : Data) :
    Runs selected (cfg loop flag d)
      (cfg next flag (((d.set i []).set j ((d.get i).reverse++d.get j)).set k ((d.get i).reverse++d.get k))) ((d.get i).length+1) := by
  have h := transfer₂_rel (Runs selected) (@Runs.trans selected) i j k hij hik hjk id id id loop next
    (fun v r S=>by rw [←hp]; exact ordinary_label selected loop hn (v,r) S) flag none d.get
  simpa [cfg,machine,transfer₂Store,transferStore,Function.comp_def] using h

theorem clear (flag : Bool) (i : Stack) (loop next : Label) (hp : program loop=clearStmt i loop next)
    (hn : machine.request loop=none) (d : Data) :
    Runs selected (cfg loop flag d) (cfg next flag (d.set i [])) ((d.get i).length+1) := by
  have h := clear_rel (Runs selected) (@Runs.trans selected) i loop next
    (fun v r S=>by rw [←hp]; exact ordinary_label selected loop hn (v,r) S) flag none d.get
  simpa [cfg,machine] using h

end PlanarHom.MixedParallelMachines
