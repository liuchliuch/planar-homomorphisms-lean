import PlanarHom.GraphParallelCode
import PlanarHom.OracleReductionComposition

/-! The actual fixed finite-control oracle program for graph occurrence replication. -/

namespace PlanarHom.GraphParallelMachines

open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition
open PlanarHom.BinaryArithmetic

inductive Stack | input | factor | back | vertices | edge | buffer | payload | output | count
  deriving DecidableEq, Fintype
inductive Label | factor | vertices | header | edge | reverseEdge | check | emit | restoreEdge
  | query | restoreFactor | clearEdge | reversePayload | frameCount | prefixCount | prefixVertices
  | clearFactor | halt
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

def Data.get (d : Data) : Stack → Bits
  | .input => d.input | .factor => d.factor | .back => d.back | .vertices => d.vertices
  | .edge => d.edge | .buffer => d.buffer | .payload => d.payload | .output => d.output | .count => d.count

def Data.set (d : Data) (k : Stack) (xs : Bits) : Data := match k with
  | .input => {d with input:=xs} | .factor => {d with factor:=xs} | .back => {d with back:=xs}
  | .vertices => {d with vertices:=xs} | .edge => {d with edge:=xs} | .buffer => {d with buffer:=xs}
  | .payload => {d with payload:=xs} | .output => {d with output:=xs} | .count => {d with count:=xs}

@[simp] theorem update_get (d : Data) (k : Stack) (xs : Bits) :
    Function.update d.get k xs = (d.set k xs).get := by
  funext j
  cases k <;> cases j <;> simp [Data.get,Data.set]

abbrev State := Unit × Option Bool
abbrev Statement := Stmt (fun _ : Stack=>Bool) Label State

def resetGoto (next : Label) : Statement := .load (fun _=>((),none)) (.goto (fun _=>next))

def pushParsed (dest : Option Stack) (framed : Bool) (next : Label) : Statement :=
  match dest with
  | none => resetGoto next
  | some k => if framed then
      .push k (fun _=>true) (.push k (fun v=>v.2.getD false) (resetGoto next))
    else .push k (fun v=>v.2.getD false) (resetGoto next)

def endParsed (dest : Option Stack) (framed : Bool) (next : Label) : Statement :=
  match dest with
  | none => resetGoto next
  | some k => if framed then .push k (fun _=>false) (resetGoto next) else resetGoto next

/-- Consume one escape marker and its data bit; all operations are fixed TM2 syntax. -/
def parseStmt (dest : Option Stack) (framed : Bool) (loop next : Label) : Statement :=
  .pop .input (fun v a=>(v.1,a))
    (.branch (fun v=>v.2.getD false)
      (.pop .input (fun v a=>(v.1,a)) (pushParsed dest framed loop))
      (endParsed dest framed next))

def program : Label → Statement
  | .factor => parseStmt (some .factor) false .factor .vertices
  | .vertices => parseStmt (some .vertices) true .vertices .header
  | .header => parseStmt none false .header .edge
  | .edge => .peek .input (fun v a=>(v.1,a))
      (.branch (fun v=>v.2.isSome)
        (parseStmt (some .buffer) true .edge .reverseEdge)
        (resetGoto .reversePayload))
  | .reverseEdge => transferStmt .buffer .edge id id .reverseEdge .check
  | .check => .pop .factor (fun v a=>(v.1,a))
      (.branch (fun v=>v.2.isSome)
        (.push .back (fun v=>v.2.getD false) (resetGoto .emit)) (resetGoto .restoreFactor))
  | .emit => transfer₂Stmt .edge .buffer .payload id id id .emit .restoreEdge
  | .restoreEdge => transferStmt .buffer .edge id id .restoreEdge .query
  | .query => .halt
  | .restoreFactor => transferStmt .back .factor id id .restoreFactor .clearEdge
  | .clearEdge => clearStmt .edge .clearEdge .edge
  | .reversePayload => transferStmt .payload .output id id .reversePayload .frameCount
  | .frameCount => .pop .count (fun v a=>(v.1,a))
      (.branch (fun v=>v.2.isSome)
        (.push .buffer (fun _=>true) (.push .buffer (fun v=>v.2.getD false) (resetGoto .frameCount)))
        (.push .buffer (fun _=>false) (resetGoto .prefixCount)))
  | .prefixCount => transferStmt .buffer .output id id .prefixCount .prefixVertices
  | .prefixVertices => transferStmt .vertices .output id id .prefixVertices .clearFactor
  | .clearFactor => clearStmt .factor .clearFactor .halt
  | .halt => .halt

/-- The sole oracle is bit-string successor, used to update the canonical
binary output-count header once per emitted edge occurrence. -/
def machine : OracleTM2 where
  core := {
    tm := {
      K := Stack
      Γ := fun _=>Bool
      k₀ := .input
      k₁ := .output
      Λ := Label
      main := .factor
      σ := State
      initialState := ((),none)
      Γk₀Fin := inferInstance
      m := program }
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool }
  finiteAlphabet := fun _=>inferInstance
  queryStack := .count
  answerStack := .count
  queryAlphabet := Equiv.refl Bool
  answerAlphabet := Equiv.refl Bool
  request | .query => some .check | _ => none

def cfg (l : Label) (d : Data) : machine.Cfg := ⟨some l,((),none),d.get⟩

/-- A genuine oracle run with a proved bound on its complete charged cost. -/
def Runs (c d : machine.Cfg) (bound : ℕ) : Prop :=
  ∃ s t qs, machine.Run succBits c d s t qs ∧ t ≤ bound

theorem Runs.refl (c : machine.Cfg) : Runs c c 0 := ⟨0,0,[],.refl c,by rfl⟩

theorem Runs.trans {c d e : machine.Cfg} {n k : ℕ} (h : Runs c d n) (h' : Runs d e k) :
    Runs c e (n+k) := by
  obtain ⟨s,t,qs,hr,ht⟩ := h
  obtain ⟨s',t',qs',hr',ht'⟩ := h'
  exact ⟨_,_,_,hr.trans hr',Nat.add_le_add ht ht'⟩

theorem Runs.mono {c d : machine.Cfg} {n k : ℕ} (h : Runs c d n) (hk : n ≤ k) : Runs c d k := by
  obtain ⟨s,t,qs,hr,ht⟩ := h
  exact ⟨s,t,qs,hr,ht.trans hk⟩

theorem ordinary {c d : machine.Cfg} (hn : machine.continuation c = none)
    (hs : machine.core.tm.step c = some d) : Runs c d 1 :=
  ⟨1,1,[],.ordinary hn hs (.refl d),by rfl⟩

theorem ordinary_label (l : Label) (hn : machine.request l = none)
    (v : State) (S : Stack→Bits) :
    Runs ⟨some l,v,S⟩ (stepAux (program l) v S) 1 := ordinary hn rfl

theorem transfer (i j : Stack) (hij : i ≠ j) (loop next : Label)
    (hp : program loop = transferStmt i j id id loop next) (hn : machine.request loop = none)
    (d : Data) :
    Runs (cfg loop d) (cfg next ((d.set i []).set j ((d.get i).reverse++d.get j)))
      ((d.get i).length+1) := by
  have h := transfer_rel Runs (@Runs.trans) i j hij id id loop next
    (fun v r S => by rw [←hp]; exact ordinary_label loop hn (v,r) S) () none d.get
  simpa [cfg,machine,transferStore,Function.comp_def] using h

theorem transfer₂ (i j k : Stack) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (loop next : Label) (hp : program loop = transfer₂Stmt i j k id id id loop next)
    (hn : machine.request loop = none) (d : Data) :
    Runs (cfg loop d)
      (cfg next (((d.set i []).set j ((d.get i).reverse++d.get j)).set k ((d.get i).reverse++d.get k)))
      ((d.get i).length+1) := by
  have h := transfer₂_rel Runs (@Runs.trans) i j k hij hik hjk id id id loop next
    (fun v r S => by rw [←hp]; exact ordinary_label loop hn (v,r) S) () none d.get
  simpa [cfg,machine,transfer₂Store,transferStore,Function.comp_def] using h

theorem clear (i : Stack) (loop next : Label) (hp : program loop = clearStmt i loop next)
    (hn : machine.request loop = none) (d : Data) :
    Runs (cfg loop d) (cfg next (d.set i [])) ((d.get i).length+1) := by
  have h := clear_rel Runs (@Runs.trans) i loop next
    (fun v r S => by rw [←hp]; exact ordinary_label loop hn (v,r) S) () none d.get
  simpa [cfg,machine] using h

/-- Actual polynomial-time implementation of the exact raw successor oracle. -/
noncomputable def successorBitsComputer :
    TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding BitEncoding.bits.toFinEncoding succBits where
  tm := successorMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
  outputsFun xs := by
    simpa [BitEncoding.bits,BitEncoding.toFinEncoding,Equiv.refl] using successor_outputs xs

end PlanarHom.GraphParallelMachines
