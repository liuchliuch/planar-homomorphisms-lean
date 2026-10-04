import PlanarHom.CountingCookLevinLayer

/-! Polynomial-size shared Boolean circuit family for the actual single-tape
counting source. Every layer is an explicit NOR expression family. Uniform
raw-code serialization remains a separate compiler obligation. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic

/-- This evaluator refers only to the explicit previous Boolean registers and
one input choice bit. It does not call the source machine transition function. -/
def booleanLayer (m : Machine) {L : ℕ} (v : StateBit m L → Bool) (b : Bool) : StateBit m L → Bool :=
  fun out => (stepLayer m out).eval
    (Expr.grounded (Sum.elim v (fun expected => decide (b=expected))))

theorem booleanLayer_correct (m : Machine) {L : ℕ} (s : ReplayState m L) (b : Bool) :
    booleanLayer m (stateBits m s) b=stateBits m (windowStep m s b) := by
  funext out
  exact stepLayer_correct m s b out

theorem booleanLayers_correct (m : Machine) {L : ℕ} (s : ReplayState m L) (bs : List Bool) :
    bs.foldl (booleanLayer m) (stateBits m s)=stateBits m (bs.foldl (windowStep m) s) := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons,booleanLayer_correct,ih]

/-- The final accepting bit is a constant-size Boolean conjunction. -/
def circuitAccept (m : Machine) {L : ℕ} (v : StateBit m L → Bool) : Bool :=
  v (StateBit.control m .accept) && v (StateBit.valid m true)

theorem circuitAccept_correct (m : Machine) {L : ℕ} (s : ReplayState m L) :
    circuitAccept m (stateBits m s)=finalBit m s := by
  rcases s with ⟨⟨⟨q,h⟩,left,right⟩,ok⟩
  cases q <;> cases ok <;> simp [circuitAccept,stateBits,StateBit.control,StateBit.valid,
    finalBit,acceptingWindow]

/-- Explicit shared-layer Boolean circuit on exactly `clock` witness inputs.
The initial registers are fixed constants determined by the literal input word. -/
def circuitValue (m : Machine) (x : Complexity.Bits) (clock : ℕ) (w : Fin clock → Bool) : Bool :=
  circuitAccept m ((List.ofFn w).foldl (booleanLayer m)
    (stateBits m (encodeWindow m (x.length+clock) (initial m x),true)))

theorem circuitValue_correct (m : Machine) (x : Complexity.Bits) (clock : ℕ) (w : Fin clock → Bool) :
    circuitValue m x clock w=finiteReplay m x clock w := by
  rw [circuitValue,booleanLayers_correct,circuitAccept_correct,finiteReplay_eq_fold]

/-- Full counting correctness, including one-to-one canonical padding. -/
theorem count_eq_circuitValue (M : PolynomialMachine) (x : Complexity.Bits) :
    M.count x=Fintype.card {w : Fin (M.time.eval x.length) → Bool //
      circuitValue M.machine x (M.time.eval x.length) w=true} := by
  simp_rw [circuitValue_correct]
  exact count_eq_finiteReplay M x

/-- Actual number of NOR nodes across all local templates, one complement gate
per witness bit, and three final conjunction gates. Inputs are shared registers. -/
def circuitGates (m : Machine) (N T : ℕ) : ℕ :=
  3+T*(1+∑ out : StateBit m (N+T), (stepLayer m out).gates)

def circuitGatePolynomial (m : Machine) (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 3+p*(Polynomial.C 1+Polynomial.C (localGateBound m)*
    (Polynomial.C (Fintype.card (Control m.Q)+Fintype.card m.Γ+2)+
      Polynomial.C (2*(Fintype.card m.Γ+1))*(Polynomial.X+p+Polynomial.C 1)))

/-- Explicit polynomial gate bound for every input, with only fixed alphabet
and transition-table constants depending on the source machine. -/
theorem circuitGates_le_polynomial (m : Machine) (p : Polynomial ℕ) (N : ℕ) :
    circuitGates m N (p.eval N)≤(circuitGatePolynomial m p).eval N := by
  have h := stepLayer_total_gates m (N+p.eval N)
  have hb := Nat.add_le_add_left (Nat.mul_le_mul_left (p.eval N) (Nat.add_le_add_left h 1)) 3
  simpa only [circuitGates,circuitGatePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hb

/-- A proved circuit-family consequence for every independent #P source; no
circuit-hardness hypothesis is used. The remaining endpoint is uniform circuit
serialization and its composition with the parsimonious graph compilers. -/
theorem sharpP_counting_circuits {f : Complexity.Bits → ℕ} (hf : Complexity.SharpP f) :
    ∃ M : PolynomialMachine, ∀ x,
      f x=Fintype.card {w : Fin (M.time.eval x.length) → Bool //
        circuitValue M.machine x (M.time.eval x.length) w=true} ∧
      circuitGates M.machine x.length (M.time.eval x.length)≤
        (circuitGatePolynomial M.machine M.time).eval x.length := by
  obtain ⟨M,hM⟩ := hf.singleTapeSharpP
  exact ⟨M,fun x => ⟨(hM x).trans (count_eq_circuitValue M x),
    circuitGates_le_polynomial M.machine M.time x.length⟩⟩

end PlanarHom.CountingCookLevin
