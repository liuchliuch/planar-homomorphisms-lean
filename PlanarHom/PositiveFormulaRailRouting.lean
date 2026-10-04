import PlanarHom.AdjacentRailRouting

/-! Complete logical routing of every original positive exact-one formula.
Every occurrence is copied by adjacent crossings and a fanout, original input
order is restored after each request, and triples terminate in their clause. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveFormulaRailRouting
open ParsimoniousNorOneInThree CountingCookLevin AdjacentRailRouting

/-- The three copies are inserted nearest the original rails, hence reverse
clause order at the termination port; exactly-one is invariant under reversal. -/
def gather (n : ℕ) (c : Clause ℕ) (xs : List Bool) : List Bool :=
  copyCircuit n c.2.2 (copyCircuit n c.2.1 (copyCircuit n c.1 xs))

theorem gather_correct (xs tail : List Bool) (c : Clause ℕ)
    (hc : c.1<xs.length ∧ c.2.1<xs.length ∧ c.2.2<xs.length) :
    gather xs.length c (xs++tail)=xs++xs[c.2.2]::xs[c.2.1]::xs[c.1]::tail := by
  simp only [gather,copyCircuit_correct xs tail c.1 hc.1,
    copyCircuit_correct xs (xs[c.1]::tail) c.2.1 hc.2.1,
    copyCircuit_correct xs (xs[c.2.1]::xs[c.1]::tail) c.2.2 hc.2.2]

/-- Exact semantic action of a physical three-port clause termination. -/
def terminate (n : ℕ) (xs : List Bool) : Option (List Bool) :=
  if n+3≤xs.length ∧ ExactlyOne (readBit xs n) (readBit xs (n+1)) (readBit xs (n+2))
  then some (xs.take n++xs.drop (n+3)) else none

@[simp] theorem terminate_three (xs tail : List Bool) (x y z : Bool) :
    terminate xs.length (xs++x::y::z::tail)=
      if ExactlyOne x y z then some (xs++tail) else none := by
  simp [terminate,readBit,List.getElem?_append_right,List.take_append,List.drop_append,List.drop_eq_nil_of_le (show xs.length≤xs.length+3 by omega)]

def clause (n : ℕ) (c : Clause ℕ) (xs : List Bool) : Option (List Bool) :=
  terminate n (gather n c xs)

theorem clause_correct (xs : List Bool) (c : Clause ℕ)
    (hc : c.1<xs.length ∧ c.2.1<xs.length ∧ c.2.2<xs.length) :
    clause xs.length c xs=
      if ExactlyOne (readBit xs c.1) (readBit xs c.2.1) (readBit xs c.2.2) then some xs else none := by
  have hg := gather_correct xs [] c hc
  simp only [List.append_nil] at hg
  rw [clause,hg,terminate_three]
  simp only [List.append_nil]
  have he : ExactlyOne xs[c.2.2] xs[c.2.1] xs[c.1] ↔
      ExactlyOne (readBit xs c.1) (readBit xs c.2.1) (readBit xs c.2.2) := by
    simp only [readBit,List.getElem?_eq_getElem hc.1,List.getElem?_eq_getElem hc.2.1,
      List.getElem?_eq_getElem hc.2.2,Option.getD_some,ExactlyOne]
    omega
  simp only [he]

/-- This is a serialized-order traversal; each failed clause terminates the
same candidate assignment, while accepted candidates retain every original bit. -/
def run (n : ℕ) : Formula ℕ → List Bool → Option (List Bool)
  | [],xs => some xs
  | c::cs,xs => (clause n c xs).bind (run n cs)

/-- Full formula semantics, including empty clauses lists and unused variables. -/
theorem run_correct (f : Formula ℕ) (xs : List Bool)
    (hf : NumericValid (xs.length,f)) :
    run xs.length f xs=if Satisfies f (readBit xs) then some xs else none := by
  induction f with
  | nil => simp [run,Satisfies]
  | cons c cs ih =>
    have hc := hf c (by simp)
    have hcs : NumericValid (xs.length,cs) := fun d hd => hf d (by simp [hd])
    rw [run,clause_correct xs c hc]
    have hs : Satisfies (c::cs) (readBit xs) ↔
        ExactlyOne (readBit xs c.1) (readBit xs c.2.1) (readBit xs c.2.2) ∧ Satisfies cs (readBit xs) := by
      simp [Satisfies]
    by_cases h : ExactlyOne (readBit xs c.1) (readBit xs c.2.1) (readBit xs c.2.2)
    · simp only [if_pos h,Option.bind_some]
      rw [ih hcs]
      simp only [hs,h,true_and]
    · simp [h,hs]

/-- A simple cubic-quantity bound for the later materialized gadget emitter:
there are at most 6*n adjacent crossings and three fanouts per input clause. -/
def crossingCount (n : ℕ) (c : Clause ℕ) : ℕ :=
  2*(moveScript c.1 (n-1-c.1)).length+
  2*(moveScript c.2.1 (n-1-c.2.1)).length+
  2*(moveScript c.2.2 (n-1-c.2.2)).length

theorem crossingCount_le (n : ℕ) (c : Clause ℕ) : crossingCount n c≤6*n := by
  have h1 := copy_crossing_bound n c.1
  have h2 := copy_crossing_bound n c.2.1
  have h3 := copy_crossing_bound n c.2.2
  unfold crossingCount
  omega

end PlanarHom.PositiveFormulaRailRouting
