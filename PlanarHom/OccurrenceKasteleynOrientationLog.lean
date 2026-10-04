import PlanarHom.OccurrenceKasteleynPeeling
import PlanarHom.Complexity

/-!
# NEW proof: exact toggle-log orientation semantics

A log stores edge reversals, starting with every occurrence directed forward.
Repeated indices toggle repeatedly, so their multiplicity parity matters. This
shared definition connects the finite face solver to occurrence-skew encodings;
no claim about the lost historical log program is made without an equivalence
proof. The codec is the existing list of canonical binary natural numbers.
-/
namespace PlanarHom.MultiGraph.Kasteleyn

/-- The exact ordinary encoded list of edge indices. -/
def logCode : Complexity.BitEncoding (List Nat) := Complexity.BitEncoding.nat.list

/-- A list is a toggle history, not a set of reversed occurrences. -/
def logOrientation (log : List Nat) (e : Nat) : Bool := !((log.count e).bodd)

@[simp] theorem logOrientation_nil (e : Nat) : logOrientation [] e = true := rfl

theorem logOrientation_cons (a : Nat) (log : List Nat) (e : Nat) :
    logOrientation (a::log) e = if a=e then !(logOrientation log e) else logOrientation log e := by
  by_cases h : a=e
  · simp [logOrientation,h,Nat.bodd_succ]
  · simp [logOrientation,h]

/-- One Boolean accumulator step reads one literal stored occurrence. -/
def logBitStep (e : Nat) (bit : Bool) (a : Nat) : Bool := if a=e then !bit else bit

/-- A direct Boolean fold computes parity for an arbitrary initial orientation. -/
theorem logBitStep_foldl (e : Nat) (log : List Nat) (bit : Bool) :
    log.foldl (logBitStep e) bit = (bit ^^ (log.count e).bodd) := by
  induction log generalizing bit with
  | nil => simp
  | cons a log ih =>
    rw [List.foldl_cons,ih,List.count_cons]
    by_cases h : a=e
    · simp only [h,beq_self_eq_true,ite_true,Nat.bodd_succ,logBitStep]
      cases bit <;> cases (List.count e log).bodd <;> rfl
    · simp [logBitStep,h]

/-- Machine-friendly fold characterization of the public log semantics. -/
theorem logOrientation_eq_foldl (log : List Nat) (e : Nat) :
    logOrientation log e = log.foldl (logBitStep e) true := by
  rw [logBitStep_foldl]
  simp [logOrientation]

/-- Literal append composes toggle histories, including repeated bridge entries. -/
theorem logOrientation_append (xs ys : List Nat) (e : Nat) :
    logOrientation (xs++ys) e =
      ys.foldl (logBitStep e) (logOrientation xs e) := by
  rw [logOrientation_eq_foldl,List.foldl_append,← logOrientation_eq_foldl]

@[simp] theorem logOrientation_double_cons (a : Nat) (log : List Nat) :
    logOrientation (a::a::log) = logOrientation log := by
  funext e
  simp only [logOrientation_cons]
  by_cases h : a=e <;> simp [h]

/-- Indices not mentioned by the log retain their original forward orientation. -/
theorem logOrientation_of_not_mem (log : List Nat) (e : Nat) (h : e ∉ log) :
    logOrientation log e = true := by
  simp [logOrientation,List.count_eq_zero_of_not_mem h]

end PlanarHom.MultiGraph.Kasteleyn
