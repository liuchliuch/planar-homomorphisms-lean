import PlanarHom.PromisedFPReductionClosure

/-! NEW represented-output computation model for the Appendix A field codec.
All valid answer representations are accepted. Oracle time is charged against
literal reply volume; query count and query lengths have independent input
polynomial bounds, preventing replies from hiding exponentially many queries.
No canonical representative, sign oracle or field arithmetic is postulated. -/
noncomputable section
namespace PlanarHom.RepresentedBit
open Complexity PlanarHom.MachineComposition

structure Problem where
  valid : Bits→Prop
  answer : Bits→Bits→Prop

/-- An actual ordinary machine chooses a correct representative on every
promised raw input. The witness includes the full bit-time computation. -/
def Problem.InFP (P:Problem) : Prop :=
  ∃f:{x:Bits // P.valid x}→Bits,
    FP (BitEncoding.bits.restrict P.valid) BitEncoding.bits f ∧
    ∀x,P.answer x.val (f x)

def ofCanonical (P:PromiseProblem) : Problem := ⟨P.valid,fun x y=>y=P.value x⟩

theorem ofCanonical_inFP_iff (P:PromiseProblem) : (ofCanonical P).InFP ↔ P.InFP := by
  constructor
  · rintro ⟨f,hf,h⟩
    exact hf.congr h
  · intro h
    exact ⟨fun x=>P.value x.val,h,fun _=>rfl⟩

/-- The sum charges all replies, including redundant padding. -/
def replyVolume (qs:OracleTM2.Transcript) : ℕ := (qs.map (fun p=>p.2.length)).sum

/-- One uniform finite oracle machine works for every semantically correct
oracle, with no restriction on its choice or size of valid representatives. -/
structure Reduction (P Q:Problem) where
  machine : OracleTM2
  work : Polynomial ℕ
  queryCount : Polynomial ℕ
  querySize : Polynomial ℕ
  computes : ∀oracle:Bits→Bits,(∀q,Q.valid q→Q.answer q (oracle q))→
    ∀x,P.valid x→∃y steps cost qs,
      machine.Run oracle (machine.initial x) (machine.final y) steps cost qs ∧
      P.answer x y ∧
      (∀q a,(q,a)∈qs→Q.valid q) ∧
      qs.length≤queryCount.eval x.length ∧
      (∀q a,(q,a)∈qs→q.length≤querySize.eval x.length) ∧
      cost≤work.eval (x.length+replyVolume qs)

/-- Existing canonical reductions are faithful special cases. The old charged
run is reused, not replaced by an abstract query/cost certificate. -/
def Reduction.ofCanonical {P Q:PromiseProblem} (r:PromisePolyTimeTuringReduction P Q) :
    Reduction (ofCanonical P) (ofCanonical Q) where
  machine:=r.machine
  work:=r.time
  queryCount:=r.time
  querySize:=r.time
  computes:=by
    intro oracle ho x hx
    obtain ⟨steps,cost,qs,hr,hcost,hq⟩:=r.computes oracle ho x hx
    refine ⟨P.value x,steps,cost,qs,hr,rfl,hq,?_,?_,?_⟩
    · exact hr.query_count_le.trans hcost
    · intro q a hqa
      exact (Nat.le_add_right q.length a.length).trans
        ((hr.query_answer_length_le hqa).trans hcost)
    · exact hcost.trans (natPolynomial_monotone r.time (Nat.le_add_right _ _))

theorem replyVolume_le (qs:OracleTM2.Transcript) (B:ℕ)
    (h:∀q a,(q,a)∈qs→a.length≤B) : replyVolume qs≤qs.length*B := by
  induction qs with
  | nil => simp [replyVolume]
  | cons qa qs ih =>
    have ht:=ih (fun q a hqa=>h q a (List.mem_cons_of_mem _ hqa))
    have hh:=h qa.1 qa.2 (List.mem_cons_self)
    simp only [replyVolume,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    change qa.2.length+replyVolume qs≤qs.length*B+B
    omega

end PlanarHom.RepresentedBit
