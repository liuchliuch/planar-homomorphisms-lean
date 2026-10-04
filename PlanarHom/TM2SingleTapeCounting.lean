import PlanarHom.TM2SingleTapePrimitiveRuns
import PlanarHom.TM2SingleTapeInputOutput
import PlanarHom.TM2SingleTapeClock

/-! # Polynomial, accepting-path-preserving multistack-to-single-tape compilation

All simulation hypotheses below are discharged by actual local machine runs.
The polynomial bounds every computation, and counts the complete accepting tree,
including separate labelled choices with coincident successors.
-/
namespace PlanarHom.TM2SingleTapeCounting
noncomputable section
open Turing NondeterministicComputationTree NondeterministicBlockSimulation
open TM2SingleTapeCompiler TM2SingleTapePrimitiveRuns TM2SingleTapeClock
open NondeterministicTM2SpaceBounds

/-- The source space potential and concrete parallel-track tape relation. -/
def Related (m : Source) (cap fuel : ℕ) (c : m.Cfg) (d : (compile m).Cfg) : Prop :=
  Space m cap fuel c ∧ ∃ L, Represents m c L ∧ d=represented m c L

/-- Every local obligation is proved for the concrete finite single-tape compiler. -/
def simulation (m : Source) (cap : ℕ) :
    Simulation m.view (compile m).view (blockCost m (primitiveBound m) cap) where
  Related := Related m cap
  reject := by
    intro n c d hr hv
    obtain ⟨hspace,L,hL,rfl⟩ := hr
    obtain ⟨hl,ho⟩ := reject_inv m hv
    obtain ⟨e,run,he⟩ := halt_represented_run m c L hl hL
    exact ⟨2,e,blockCost_two_le _ _ _,run,by simpa [ho] using he⟩
  accept := by
    intro n c d hr hv
    obtain ⟨hspace,L,hL,rfl⟩ := hr
    obtain ⟨hl,ho⟩ := accept_inv m hv
    obtain ⟨e,run,he⟩ := halt_represented_run m c L hl hL
    exact ⟨2,e,blockCost_two_le _ _ _,run,by simpa [ho] using he⟩
  ordinary := by
    intro n c next d hr hv
    obtain ⟨hspace,L,hL,rfl⟩ := hr
    obtain ⟨l,hl,hb,rfl⟩ := ordinary_inv m hv
    obtain ⟨size,hsize,hcap⟩ := hspace
    obtain ⟨t,L',hL',run,ht⟩ := source_step m c l hl hb L hL size hsize
    refine ⟨t,represented m (TM2.stepAux (m.core.tm.m l) c.var c.stk) L',
      ht.trans (statement_cost_le m (primitiveBound m) cap size l (by omega)),run,?_,L',hL',rfl⟩
    exact ordinary_space m ⟨size,hsize,hcap⟩ hv
  binary := by
    intro n c left right d hr hv
    obtain ⟨hspace,L,hL,rfl⟩ := hr
    obtain ⟨l,a,b,hl,hb,rfl,rfl⟩ := binary_inv m hv
    refine ⟨0,represented m c L,represented m (m.jump c a) L,
      represented m (m.jump c b) L,?_,.nil _,binary_step m c l a b hl hb L,
      ⟨jump_space m hspace a,L,hL,rfl⟩,⟨jump_space m hspace b,L,hL,rfl⟩⟩
    exact (by omega : 0+1≤2).trans (blockCost_two_le _ _ _)

/-- The simulation covers accepting and rejecting branches at a shared clock. -/
theorem represented_correct (m : Source) {fuel cap : ℕ} (c : m.Cfg)
    (halt : Bounded m.view c fuel) (space : Space m cap fuel c)
    (L : ListBlank (∀k,Option (m.core.tm.Γ k))) (hL : Represents m c L) :
    Bounded (compile m).view (represented m c L)
      ((fuel+1)*blockCost m (primitiveBound m) cap) ∧
    acceptingCount (compile m).view ((fuel+1)*blockCost m (primitiveBound m) cap)
      (represented m c L) = acceptingCount m.view fuel c :=
  (simulation m cap).correct halt ⟨space,L,hL,rfl⟩

/-- Actual binary input conversion followed by the complete bounded simulation.
Unused input-loader allowance is clock padding and introduces no new paths. -/
theorem input_correct (m : Source) (x : Complexity.Bits) (fuel : ℕ)
    (halt : Bounded m.view (m.initial x) fuel) :
    let clock := x.length+3+(fuel+1)*
      blockCost m (primitiveBound m) (x.length+fuel*pushConstant m)
    Bounded (compile m).view ((compile m).initial x) clock ∧
      acceptingCount (compile m).view clock ((compile m).initial x) =
        acceptingCount m.view fuel (m.initial x) := by
  dsimp only
  obtain ⟨L,hL,pre,hpre⟩ := input_represented_run m x
  obtain ⟨hb,hc⟩ := represented_correct m (m.initial x) halt (initial_space m x fuel) L hL
  have hb' := pre.bounded hb
  have hle : inputCost x + (fuel+1)*blockCost m (primitiveBound m)
      (x.length+fuel*pushConstant m) ≤
      x.length+3+(fuel+1)*blockCost m (primitiveBound m) (x.length+fuel*pushConstant m) :=
    Nat.add_le_add_right hpre _
  refine ⟨hb'.mono hle,?_⟩
  rw [hb'.acceptingCount_eq_of_le hle,pre.count,hc]

/-- A genuine conventional single-tape NTM with an explicit polynomial clock. -/
def polynomialCompile (M : Complexity.PolynomialNondeterministicMachine) :
    SingleTapeNondeterministic.PolynomialMachine where
  machine := compile M.machine
  time := TM2SingleTapeClock.time M.machine (primitiveBound M.machine) M.time
  halts x := by
    simpa only [time_eval] using (input_correct M.machine x (M.time.eval x.length) (M.halts x)).1

/-- Parsimonious compiler: equality counts all complete accepting computations. -/
theorem polynomialCompile_count (M : Complexity.PolynomialNondeterministicMachine)
    (x : Complexity.Bits) : (polynomialCompile M).count x = M.count x := by
  simpa only [SingleTapeNondeterministic.PolynomialMachine.count,polynomialCompile,
    Complexity.PolynomialNondeterministicMachine.count,time_eval] using
    (input_correct M.machine x (M.time.eval x.length) (M.halts x)).2

/-- The equality is an equality of all complete accepting computations; neither
side is a certificate count or a count restricted to a selected set of paths. -/
theorem complete_path_card (M : Complexity.PolynomialNondeterministicMachine)
    (x : Complexity.Bits) :
    letI := ((polynomialCompile M).halts x).completePathsFintype
    letI := (M.halts x).completePathsFintype
    Fintype.card (Σ n, AcceptingPath (polynomialCompile M).machine.view
      ((polynomialCompile M).machine.initial x) n) =
    Fintype.card (Σ n, AcceptingPath M.machine.view (M.machine.initial x) n) := by
  letI := ((polynomialCompile M).halts x).completePathsFintype
  letI := (M.halts x).completePathsFintype
  rw [← (polynomialCompile M).count_eq_card_complete_paths x,
    ← M.count_eq_card_complete_paths x]
  exact polynomialCompile_count M x

end
end PlanarHom.TM2SingleTapeCounting
