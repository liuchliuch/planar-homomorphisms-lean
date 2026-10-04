import PlanarHom.TM1FiniteControl
import PlanarHom.TM2SingleTapeLoading
import PlanarHom.TM2TapeBoundaryRuns

/-! # Finite local single-tape implementation of binary-choice multistack machines

The tape alphabet tags raw input separately from the parallel stack tracks.
Finite residual syntax implements every scan and stack operation by local
read/write/move transitions. Only source binary labels create binary target nodes.
-/
namespace PlanarHom.TM2SingleTapeCompiler
noncomputable section
open Turing NondeterministicComputationTree NondeterministicBlockSimulation
open SingleTapeNondeterministic

abbrev Source := NondeterministicTM2.Machine

instance sourceStackFinite (m : Source) : Fintype m.core.tm.K := m.core.tm.kFin
instance sourceLabelFinite (m : Source) : Fintype m.core.tm.Λ := m.core.tm.ΛFin
instance sourceStateFinite (m : Source) : Fintype m.core.tm.σ := m.core.tm.σFin
instance sourceAlphabetFinite (m : Source) : ∀ k, Fintype (m.core.tm.Γ k) := m.finiteAlphabet
instance sourceLabelInhabited (m : Source) : Inhabited m.core.tm.Λ := ⟨m.core.tm.main⟩

abbrev SimAlphabet (m : Source) := TM2to1.Γ' m.core.tm.K m.core.tm.Γ
abbrev SimLabel (m : Source) := TM2to1.Λ' m.core.tm.K m.core.tm.Γ m.core.tm.Λ m.core.tm.σ
abbrev SimCfg (m : Source) := TM1.Cfg (SimAlphabet m) (SimLabel m) m.core.tm.σ
abbrev Alphabet (m : Source) := TM2SingleTapeLoading.Alphabet m.core.tm.K m.core.tm.Γ

def program (m : Source) : SimLabel m → TM1.Stmt (SimAlphabet m) (SimLabel m) m.core.tm.σ :=
  TM2to1.tr m.core.tm.m

def support (m : Source) : Finset (SimLabel m) := TM2to1.trSupp m.core.tm.m Finset.univ

theorem supported (m : Source) : TM1.Supports (program m) (support m) := by
  apply TM2to1.tr_supports
  refine ⟨Finset.mem_univ _,fun l _ => ?_⟩
  induction m.core.tm.m l <;> simp_all [TM2.SupportsStmt]

theorem normal_mem (m : Source) (l : m.core.tm.Λ) : TM2to1.Λ'.normal l ∈ support m := by
  classical
  exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,Finset.mem_insert_self _ _⟩

abbrev CoreState (m : Source) := TM1FiniteControl.State (program m) (support m)
abbrev CoreCfg (m : Source) := TM1FiniteControl.Cfg (program m) (support m)
abbrev State (m : Source) :=
  (TM2SingleTapeLoading.LoaderState ⊕ TM2SingleTapeLoading.CheckerState) ⊕ CoreState m

abbrev load {m : Source} (q : TM2SingleTapeLoading.LoaderState) : State m := .inl (.inl q)
abbrev check {m : Source} (q : TM2SingleTapeLoading.CheckerState) : State m := .inl (.inr q)
abbrev core {m : Source} (q : CoreState m) : State m := .inr q

def sourceState (m : Source) (l : m.core.tm.Λ) (v : m.core.tm.σ) : CoreState m :=
  (.inl ⟨.normal l,normal_mem m l⟩,v)

def initialState (m : Source) : CoreState m := sourceState m m.core.tm.main m.core.tm.initialState

def mirrorTape (m : Source) (t : Tape (SimAlphabet m)) : Tape (Alphabet m) :=
  TapeMirrorCompiler.mirror (t.map TM2SingleTapeLoading.embedding)

def command (m : Source) (a : SimAlphabet m) (q : CoreState m) : TM0.Stmt (SimAlphabet m) →
    Action (Alphabet m) (State m)
  | .move .left => ⟨.sim a,.right,.run (core q)⟩
  | .move .right => ⟨.sim a,.left,.run (core q)⟩
  | .write b => ⟨.sim b,.stay,.run (core q)⟩

def checker (m : Source) (q : TM2SingleTapeLoading.CheckerState) (a : Alphabet m) :
    Action (Alphabet m) (State m) := by
  classical
  exact TM2SingleTapeLoading.mapAction check
    (TM2SingleTapeLoading.checkerAction m.core.tm.k₁ (m.core.outputAlphabet.symm true) q a)

def primitive (m : Source) (q : CoreState m) : Alphabet m → Instruction (Alphabet m) (State m)
  | .raw b => .ordinary ⟨.raw b,.stay,.reject⟩
  | .sim a => match TM1FiniteControl.transition (program m) (support m) (supported m) q a with
    | none => .ordinary ⟨.sim a,.stay,.reject⟩
    | some (r,s) => .ordinary (command m a r s)

def coreInstruction (m : Source) (q : CoreState m) (a : Alphabet m) :
    Instruction (Alphabet m) (State m) :=
  match q.1 with
  | .inl l => match l.val with
    | .normal l => match m.branch l with
      | none => primitive m q a
      | some (left,right) => .binary
          ⟨a,.stay,.run (core (sourceState m left q.2))⟩
          ⟨a,.stay,.run (core (sourceState m right q.2))⟩
    | _ => primitive m q a
  | .inr r => match r.val with
    | none => .ordinary (checker m .first a)
    | some _ => primitive m q a

def instruction (m : Source) : State m → Alphabet m → Instruction (Alphabet m) (State m)
  | .inl (.inl .done),a => .ordinary ⟨a,.stay,.run (core (initialState m))⟩
  | .inl (.inl q),a => .ordinary (TM2SingleTapeLoading.mapAction load
      (TM2SingleTapeLoading.loaderAction m.core.tm.k₀ m.core.inputAlphabet.symm q a))
  | .inl (.inr q),a => .ordinary (checker m q a)
  | .inr q,a => coreInstruction m q a

/-- The actual finite-alphabet finite-control conventional single-tape machine. -/
def compile (m : Source) : Machine where
  Γ := Alphabet m
  Q := State m
  blank := default
  input := .raw
  input_injective := TM2SingleTapeLoading.raw_injective
  input_ne_blank := TM2SingleTapeLoading.raw_ne_blank
  start := load (.scan false)
  transition := instruction m

/-- Embed an actual finite core configuration into the local tape machine. -/
def embed (m : Source) (c : CoreCfg m) : (compile m).Cfg :=
  (.run (core c.1),mirrorTape m c.2)

/-- Every emitted command acts on precisely one tape cell and mirrors movement. -/
theorem command_correct (m : Source) (q : CoreState m) (s : TM0.Stmt (SimAlphabet m))
    (t : Tape (SimAlphabet m)) :
    (compile m).execute (command m t.head q s) (mirrorTape m t) =
      embed m (q,TM1FiniteControl.applyStmt s t) := by
  have hw : (mirrorTape m t).write (.sim t.head) = mirrorTape m t := by
    exact Tape.write_self (mirrorTape m t)
  cases s with
  | move d =>
    cases d <;> simp only [Machine.execute,command,embed,TM1FiniteControl.applyStmt] <;> rw [hw] <;>
      simp only [mirrorTape,Tape.map_move,TapeMirrorCompiler.mirror_move,TapeMirrorCompiler.direction]
  | write b =>
    simp [Machine.execute,command,embed,mirrorTape,TM1FiniteControl.applyStmt,
      TapeMirrorCompiler.mirror_write,Tape.map_write,TM2SingleTapeLoading.embedding]

/-- Pack a supported TM1 boundary into the complete target machine. -/
def boundary (m : Source) (c : SimCfg m) (hc : c.l ∈ Finset.insertNone (support m)) :
    (compile m).Cfg :=
  embed m (TM1FiniteControl.startBoundary (program m) (support m) c hc)

theorem normal_option_mem (m : Source) (l : Option m.core.tm.Λ) :
    l.map TM2to1.Λ'.normal ∈ Finset.insertNone (support m) := by
  cases l with
  | none => simp
  | some l => exact Finset.some_mem_insertNone.mpr (normal_mem m l)

/-- The mirrored parallel-track tape at a source instruction boundary. -/
def represented (m : Source) (c : m.Cfg)
    (L : ListBlank (∀ k, Option (m.core.tm.Γ k))) : (compile m).Cfg :=
  boundary m ⟨c.l.map TM2to1.Λ'.normal,c.var,Tape.mk' ∅ (TM2to1.addBottom L)⟩
    (normal_option_mem m c.l)

def Represents (m : Source) (c : m.Cfg)
    (L : ListBlank (∀ k, Option (m.core.tm.Γ k))) : Prop :=
  ∀ k, L.map (proj k) = ListBlank.mk ((c.stk k).map some).reverse

/-- Both target binary edges remain present even if their continuations agree. -/
theorem binary_step (m : Source) (c : m.Cfg) (l left right : m.core.tm.Λ)
    (hl : c.l=some l) (hb : m.branch l=some (left,right))
    (L : ListBlank (∀ k, Option (m.core.tm.Γ k))) :
    (compile m).view (represented m c L) =
      .binary (represented m (m.jump c left) L) (represented m (m.jump c right) L) := by
  rcases c with ⟨cl,v,S⟩
  simp only at hl
  subst cl
  simp [represented,boundary,embed,TM1FiniteControl.startBoundary,TM1FiniteControl.startEntry,
    Machine.view,compile,instruction,coreInstruction,hb,sourceState,Machine.execute,
    NondeterministicTM2.Machine.jump,Tape.write_self]

end
end PlanarHom.TM2SingleTapeCompiler
