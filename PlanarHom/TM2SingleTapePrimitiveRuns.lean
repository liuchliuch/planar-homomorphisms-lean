import PlanarHom.TM2SingleTapeCompiler

/-! # Ordinary primitive blocks in the finite conventional tape compiler -/
namespace PlanarHom.TM2SingleTapePrimitiveRuns
noncomputable section
open Turing NondeterministicComputationTree NondeterministicBlockSimulation
open TM2SingleTapeCompiler TM1FiniteControl SingleTapeNondeterministic

/-- One fixed finite maximum, conservatively expressed as a sum. -/
def primitiveBound (m : Source) : ℕ :=
  ∑ l∈support m, TM1PrimitiveTimeBounds.bound (program m l)

theorem primitiveBound_le (m : Source) (l : SimLabel m) (hl : l∈support m) :
    TM1PrimitiveTimeBounds.bound (program m l)≤primitiveBound m :=
  by
    simpa only [primitiveBound] using Finset.single_le_sum
      (f := fun l => TM1PrimitiveTimeBounds.bound (program m l)) (fun _ _ => Nat.zero_le _) hl

@[simp] theorem mirrorTape_head (m : Source) (t : Tape (SimAlphabet m)) :
    (mirrorTape m t).head=.sim t.head := rfl

/-- Execute one local primitive whenever the wrapper dispatches to the core. -/
theorem primitive_ordinary (m : Source) (c d : CoreCfg m)
    (hc : coreInstruction m c.1 (.sim c.2.head)=primitive m c.1 (.sim c.2.head))
    (hs : step (program m) (support m) (supported m) c=some d) :
    (compile m).view (embed m c)=.ordinary (embed m d) := by
  obtain ⟨⟨r,s⟩,ht,rfl⟩ := Option.map_eq_some_iff.mp hs
  simp only [Machine.view,embed,compile,TM2SingleTapeCompiler.instruction,core]
  rw [mirrorTape_head,hc]
  simp only [primitive,ht]
  exact congrArg NodeView.ordinary (command_correct m r s c.2)

/-- All residual syntax edges are ordinary, including the edge into a boundary. -/
theorem residual_ordinary (m : Source) {c d : CoreCfg m}
    (hs : residualStep (program m) (support m) (supported m) c=some d) :
    (compile m).view (embed m c)=.ordinary (embed m d) := by
  rcases c with ⟨⟨q,v⟩,t⟩
  cases q with
  | inl l => cases hs
  | inr r =>
    rcases r with ⟨r,hr⟩
    cases r with
    | none => cases hs
    | some q => exact primitive_ordinary m _ d rfl hs

/-- A source entry is ordinary exactly when it has no binary branch.
Simulator go/return entries are always ordinary. -/
def ordinaryLabel (m : Source) : SimLabel m → Prop
  | .normal l => m.branch l=none
  | .go _ _ _ => True
  | .ret _ => True

theorem entry_instruction (m : Source) (l : SimLabel m) (hl : l∈support m)
    (v : m.core.tm.σ) (a : SimAlphabet m) (h : ordinaryLabel m l) :
    coreInstruction m (.inl ⟨l,hl⟩,v) (.sim a)=primitive m (.inl ⟨l,hl⟩,v) (.sim a) := by
  cases l with
  | normal l => change m.branch l=none at h; simp [coreInstruction,h]
  | go k act q => rfl
  | ret q => rfl

/-- A complete macro instruction is a block of actual conventional local edges. -/
theorem entry_run (m : Source) (l : SimLabel m) (hl : l∈support m)
    (v : m.core.tm.σ) (t : Tape (SimAlphabet m)) (h : ordinaryLabel m l) :
    OrdinaryRun (compile m).view (TM1PrimitiveTimeBounds.steps (program m l) v t)
      (TM2SingleTapeCompiler.boundary m ⟨some l,v,t⟩ (Finset.some_mem_insertNone.mpr hl))
      (TM2SingleTapeCompiler.boundary m (TM1.stepAux (program m l) v t)
        (supports_stepAux (support m) (program m l) ((supported m).2 l hl) v t)) := by
  exact TM1FiniteControl.entry_run (program m) (support m) (supported m)
    (compile m).view (embed m) (residual_ordinary m) l hl v t
    (fun hs => primitive_ordinary m _ _ (entry_instruction m l hl v t.head h) hs)

/-- Internal scan edges are genuine supported TM1 steps. -/
theorem scan_step (m : Source) {c d : SimCfg m}
    (hs : TM2TapeBoundaryRuns.scanView m.core.tm.m c=.ordinary d) :
    TM1.step (program m) c=some d := by
  rcases c with ⟨l,v,t⟩
  cases l with
  | none => cases hs
  | some l =>
    cases l with
    | normal l => cases hs
    | go k a q => exact congrArg some (NodeView.ordinary.inj hs)
    | ret q => exact congrArg some (NodeView.ordinary.inj hs)

theorem scan_supported (m : Source) {c d : SimCfg m}
    (hc : c.l∈Finset.insertNone (support m))
    (hs : TM2TapeBoundaryRuns.scanView m.core.tm.m c=.ordinary d) :
    d.l∈Finset.insertNone (support m) :=
  TM1.step_supports (program m) (supported m) (scan_step m hs) hc

/-- One internal simulator transition refines to at most the fixed syntax sum. -/
theorem scan_step_run (m : Source) {c d : SimCfg m}
    (hc : c.l∈Finset.insertNone (support m))
    (hs : TM2TapeBoundaryRuns.scanView m.core.tm.m c=.ordinary d) :
    ∃ n, n≤primitiveBound m ∧ OrdinaryRun (compile m).view n (TM2SingleTapeCompiler.boundary m c hc)
      (TM2SingleTapeCompiler.boundary m d (scan_supported m hc hs)) := by
  rcases c with ⟨l,v,t⟩
  cases l with
  | none => cases hs
  | some l =>
    have hl := Finset.some_mem_insertNone.mp hc
    have hd : ordinaryLabel m l := by
      cases l with
      | normal l => cases hs
      | go k a q => trivial
      | ret q => trivial
    have he : d=TM1.stepAux (program m l) v t := by
      exact (Option.some.inj (scan_step m hs)).symm
    subst d
    refine ⟨TM1PrimitiveTimeBounds.steps (program m l) v t,?_,?_⟩
    · exact (TM1PrimitiveTimeBounds.steps_le _ _ _).trans (primitiveBound_le m l hl)
    · exact entry_run m l hl v t hd

/-- Lift a whole internal scan trace, with one uniform primitive cost per macro edge. -/
theorem scan_run (m : Source) {n : ℕ} {c d : SimCfg m}
    (hr : OrdinaryRun (TM2TapeBoundaryRuns.scanView m.core.tm.m) n c d)
    (hc : c.l∈Finset.insertNone (support m)) :
    ∃ (hd : d.l∈Finset.insertNone (support m)) (k : ℕ),
      k≤n*primitiveBound m ∧
      OrdinaryRun (compile m).view k (TM2SingleTapeCompiler.boundary m c hc) (TM2SingleTapeCompiler.boundary m d hd) := by
  induction hr with
  | nil c => exact ⟨hc,0,Nat.zero_le _,.nil _⟩
  | @cons n c next d hs hr ih =>
    have hn := scan_supported m hc hs
    obtain ⟨hd,k,hk,run⟩ := ih hn
    obtain ⟨j,hj,pre⟩ := scan_step_run m hc hs
    exact ⟨hd,j+k,by nlinarith,pre.trans run⟩

/-- Recover the concrete tape representation from mathlib's relation. -/
theorem representation_data (m : Source) {c : m.Cfg} {d : SimCfg m}
    (h : TM2to1.TrCfg c d) :
    ∃ L, Represents m c L ∧
      d=⟨c.l.map TM2to1.Λ'.normal,c.var,Tape.mk' ∅ (TM2to1.addBottom L)⟩ := by
  cases h with
  | mk L hL => exact ⟨L,hL,rfl⟩

/-- One ordinary source instruction is implemented by a bounded run of actual
conventional tape transitions, ending at the exact represented source result. -/
theorem source_step (m : Source) (c : m.Cfg) (l : m.core.tm.Λ)
    (hl : c.l=some l) (hb : m.branch l=none)
    (L : ListBlank (∀ k,Option (m.core.tm.Γ k))) (hL : Represents m c L)
    (s : ℕ) (hS : ∀ k,(c.stk k).length≤s) :
    ∃ (t : ℕ) (L' : ListBlank (∀ k,Option (m.core.tm.Γ k))),
      Represents m (TM2.stepAux (m.core.tm.m l) c.var c.stk) L' ∧
      OrdinaryRun (compile m).view t (represented m c L)
        (represented m (TM2.stepAux (m.core.tm.m l) c.var c.stk) L') ∧
      t≤primitiveBound m*(1+TM2TapeStatementBounds.stackOps (m.core.tm.m l)*
        (2*(s+MachineComposition.pushBound (m.core.tm.m l))+3)) := by
  rcases c with ⟨cl,v,S⟩
  simp only at hl
  subst cl
  let tape := Tape.mk' ∅ (TM2to1.addBottom L)
  have hf := entry_run m (.normal l) (normal_mem m l) v tape hb
  have hc0 : (TM1.stepAux (TM2to1.trNormal (m.core.tm.m l)) v tape).l∈
      Finset.insertNone (support m) :=
    supports_stepAux (support m) (program m (.normal l))
      ((supported m).2 (.normal l) (normal_mem m l)) v tape
  obtain ⟨n,d,hd,hn,hr⟩ := TM2TapeBoundaryRuns.residual m.core.tm.m (m.core.tm.m l) v S L hL s hS
  obtain ⟨hsup,k,hk,run⟩ := scan_run m hr hc0
  obtain ⟨L',hL',rfl⟩ := representation_data m hd
  refine ⟨TM1PrimitiveTimeBounds.steps (program m (.normal l)) v tape+k,L',hL',?_,?_⟩
  · exact hf.trans run
  · have hj := (TM1PrimitiveTimeBounds.steps_le (program m (.normal l)) v tape).trans
      (primitiveBound_le m (.normal l) (normal_mem m l))
    calc
      _ ≤ primitiveBound m+n*primitiveBound m := Nat.add_le_add hj hk
      _ = primitiveBound m*(1+n) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add_left hn 1)

end
end PlanarHom.TM2SingleTapePrimitiveRuns
