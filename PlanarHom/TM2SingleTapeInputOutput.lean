import PlanarHom.TM2SingleTapeCompiler
import PlanarHom.TM2SingleTapeLoadingRuns

/-! # Exact input and output blocks of the actual reverse compiler -/
namespace PlanarHom.TM2SingleTapeCompiler
noncomputable section
open Turing SingleTapeNondeterministic NondeterministicComputationTree
  NondeterministicBlockSimulation TM2SingleTapeLoading

local instance (m : Source) : DecidableEq (m.core.tm.Γ m.core.tm.k₁) := Classical.decEq _

def loadCfg (m : Source) (c : Control LoaderState × Tape (Alphabet m)) : (compile m).Cfg :=
  (mapControl load c.1, c.2)

theorem load_view (m : Source) (q : LoaderState) (t : Tape (Alphabet m)) (hq : q ≠ .done) :
    (compile m).view (loadCfg m (.run q, t)) =
      .ordinary (loadCfg m (loaderStep m.core.tm.k₀ m.core.inputAlphabet.symm (.run q, t))) := by
  cases q with
  | done => exact (hq rfl).elim
  | scan seen =>
    change NodeView.ordinary (execute (mapAction load (loaderAction _ _ (.scan seen) t.head)) t) = _
    rw [execute_mapAction]
    rfl
  | mark =>
    change NodeView.ordinary (execute (mapAction load (loaderAction _ _ .mark t.head)) t) = _
    rw [execute_mapAction]
    rfl

def inputCost (x : List Bool) : ℕ := (if x = [] then 1 else x.length + 2) + 1

/-- Every binary input reaches the initial source boundary by genuine ordinary
transitions, including a single local transfer from loader completion. -/
theorem input_run (m : Source) (x : List Bool) :
    OrdinaryRun (compile m).view (inputCost x) ((compile m).initial x)
      (.run (core (initialState m)), loaded m.core.tm.k₀ m.core.inputAlphabet.symm x) := by
  have hr := loader_run m.core.tm.k₀ m.core.inputAlphabet.symm
    (compile m).view (loadCfg m) (load_view m) x
  apply hr.trans
  apply OrdinaryRun.cons
    (show (compile m).view (loadCfg m (.run .done,
      loaded m.core.tm.k₀ m.core.inputAlphabet.symm x)) = .ordinary
      (.run (core (initialState m)), loaded m.core.tm.k₀ m.core.inputAlphabet.symm x) by
        simp only [Machine.view, loadCfg, mapControl, compile, instruction, Machine.execute,
          Tape.write_self])
  exact .nil _

theorem inputCost_le (x : List Bool) : inputCost x ≤ x.length + 3 := by
  unfold inputCost
  split <;> omega

def haltState (m : Source) (v : m.core.tm.σ) : CoreState m :=
  (.inr ⟨none, by simp [TM1.stmts]⟩,v)

def checkControl (m : Source) (v : m.core.tm.σ) : Control CheckerState → Control (State m)
  | .run .first => .run (core (haltState m v))
  | .run (.second b) => .run (check (.second b))
  | .accept => .accept
  | .reject => .reject

def checkCfg (m : Source) (v : m.core.tm.σ)
    (c : Control CheckerState × Tape (Alphabet m)) : (compile m).Cfg :=
  (checkControl m v c.1,c.2)

theorem check_view (m : Source) (v : m.core.tm.σ) (q : CheckerState)
    (t : Tape (Alphabet m)) :
    (compile m).view (checkCfg m v (.run q,t)) = .ordinary
      (checkCfg m v (checkerStep m.core.tm.k₁ (m.core.outputAlphabet.symm true) (.run q,t))) := by
  classical
  cases q with
  | first =>
    change NodeView.ordinary (execute (mapAction check
      (checkerAction m.core.tm.k₁ (m.core.outputAlphabet.symm true) .first t.head)) t) = _
    rw [execute_mapAction]
    cases h : t.head <;>
      simp only [checkerStep, h, checkerAction, execute, Prod.map, mapControl,
        checkCfg, checkControl, id_eq]
  | second b =>
    change NodeView.ordinary (execute (mapAction check
      (checkerAction m.core.tm.k₁ (m.core.outputAlphabet.symm true) (.second b) t.head)) t) = _
    rw [execute_mapAction]
    simp only [checkerStep, checkerAction, execute, checkCfg, Prod.map]
    split_ifs <;> rfl

theorem output_singleton (m : Source) (S : List (m.core.tm.Γ m.core.tm.k₁)) :
    S.map m.core.outputAlphabet = [true] ↔ S = [m.core.outputAlphabet.symm true] := by
  constructor
  · intro h
    apply List.map_injective_iff.mpr m.core.outputAlphabet.injective
    simpa using h
  · rintro rfl
    simp

/-- The first checker instruction is dispatched directly at the finite halt
boundary, so the entire output decision costs exactly two local transitions. -/
theorem output_run (m : Source) (v : m.core.tm.σ)
    (L : ListBlank (∀ j, Option (m.core.tm.Γ j)))
    (S : List (m.core.tm.Γ m.core.tm.k₁))
    (hL : L.map (proj m.core.tm.k₁) = ListBlank.mk (S.map some).reverse) :
    OrdinaryRun (compile m).view 2
      (embed m (haltState m v, Tape.mk' ∅ (TM2to1.addBottom L)))
      (if S.map m.core.outputAlphabet = [true] then .accept else .reject,
        (TM2SingleTapeLoading.represented L).move .left) := by
  classical
  have hr := checker_run m.core.tm.k₁ (compile m).view (m.core.outputAlphabet.symm true)
    (checkCfg m v) (check_view m v) L S hL
  by_cases hs : S = [m.core.outputAlphabet.symm true]
  · have hm := (output_singleton m S).mpr hs
    simpa [hm, hs, checkCfg, checkControl, embed, mirrorTape,
      TM2SingleTapeLoading.represented] using hr
  · have hm : S.map m.core.outputAlphabet ≠ [true] := fun h => hs ((output_singleton m S).mp h)
    simpa only [hs, hm, if_false, checkCfg, checkControl, embed, mirrorTape,
      TM2SingleTapeLoading.represented] using hr

theorem initial_representation (m : Source) (x : List Bool) :
    ∃ L, Represents m (m.initial x) L ∧
      Tape.mk₁ (TM2to1.trInit m.core.tm.k₀ (x.map m.core.inputAlphabet.symm)) =
        Tape.mk' ∅ (TM2to1.addBottom L) := by
  have hi := TM2to1.trCfg_init (Λ := m.core.tm.Λ) (σ := m.core.tm.σ)
    m.core.tm.k₀ (x.map m.core.inputAlphabet.symm)
  have he : TM2.init m.core.tm.k₀ (x.map m.core.inputAlphabet.symm) = m.initial x := by
    unfold TM2.init NondeterministicTM2.Machine.initial initList
    congr 1
    funext j
    by_cases h : j = m.core.tm.k₀
    · subst j
      simp
    · simp [h]
  rw [he] at hi
  have extract {c : SimCfg m} (h : TM2to1.TrCfg (m.initial x) c) :
      ∃ L, Represents m (m.initial x) L ∧ c.Tape = Tape.mk' ∅ (TM2to1.addBottom L) := by
    cases h with
    | mk L hL => exact ⟨L, hL, rfl⟩
  exact extract hi

/-- Initial conversion ends at the same represented boundary used by every
source-step simulation. The complete input overhead is at most `n+3`. -/
theorem input_represented_run (m : Source) (x : List Bool) :
    ∃ L, Represents m (m.initial x) L ∧
      OrdinaryRun (compile m).view (inputCost x) ((compile m).initial x)
        (represented m (m.initial x) L) ∧ inputCost x ≤ x.length + 3 := by
  obtain ⟨L,hL,ht⟩ := initial_representation m x
  refine ⟨L,hL,?_,inputCost_le x⟩
  have hr := input_run m x
  rw [loaded, ht] at hr
  simpa only [represented,boundary,embed,mirrorTape,NondeterministicTM2.Machine.initial,
    initList, TM1FiniteControl.startBoundary,TM1FiniteControl.startEntry,
    initialState,sourceState] using hr

/-- Halting decisions are made by two actual tape transitions from precisely
the compiler representation of the halted source configuration. -/
theorem halt_represented_run (m : Source) (c : m.Cfg)
    (L : ListBlank (∀ j, Option (m.core.tm.Γ j)))
    (hl : c.l = none) (hL : Represents m c L) :
    ∃ d, OrdinaryRun (compile m).view 2 (represented m c L) d ∧
      (compile m).view d = if m.output c = [true] then .accept else .reject := by
  classical
  refine ⟨(if m.output c = [true] then .accept else .reject,
    (TM2SingleTapeLoading.represented L).move .left), ?_, ?_⟩
  · have hr := output_run m c.var L (c.stk m.core.tm.k₁) (hL _)
    rcases c with ⟨l,v,S⟩
    simp only at hl
    subst l
    simpa only [represented,boundary,embed,TM1FiniteControl.startBoundary,haltState,
      NondeterministicTM2.Machine.output] using hr
  · split_ifs <;> rfl

end
end PlanarHom.TM2SingleTapeCompiler
