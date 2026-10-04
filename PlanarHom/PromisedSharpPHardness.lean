import PlanarHom.SingleTapeSharpPBridge
import PlanarHom.OracleReductionComposition
import PlanarHom.PromiseReductionTransport
import PlanarHom.PromisedFPReductionClosure

/-!
# NEW reconstruction: promised counting hardness with actual oracle machines

The source is the established independent nondeterministic accepting-path #P
class. A single concrete reduction per source counting function must succeed
against every oracle extension and make only promised queries. This definition
is not an axiom and does not assert hardness of any graph evaluation problem.
-/
noncomputable section
namespace PlanarHom.Complexity

/-- The total raw-bit natural counting problem, with the existing exact codec. -/
def countingProblem (f : Bits → ℕ) : PromiseProblem :=
  ⟨fun _ => True, fun x => BitEncoding.nat.encode (f x)⟩

/-- Uniform promise hardness for independently defined accepting-path counts.
Every witness carries its finite machine, polynomial cost and query-validity proof. -/
def PromisedSharpPHard (P : PromiseProblem) : Prop :=
  ∀ f : Bits → ℕ, SharpP f → Nonempty (PromisePolyTimeTuringReduction (countingProblem f) P)

/-- Equivalent verifier-source formulation, using the already proved actual
nondeterministic/certificate machine compilers. -/
def PromisedCertificateSharpPHard (P : PromiseProblem) : Prop :=
  ∀ f : Bits → ℕ, CertificateSharpP f → Nonempty (PromisePolyTimeTuringReduction (countingProblem f) P)

/-- Equivalent conventional single-tape accepting-path source formulation. -/
def PromisedSingleTapeSharpPHard (P : PromiseProblem) : Prop :=
  ∀ f : Bits → ℕ, SingleTapeNondeterministic.SingleTapeSharpP f →
    Nonempty (PromisePolyTimeTuringReduction (countingProblem f) P)

theorem promisedSharpPHard_iff_certificate (P : PromiseProblem) :
    PromisedSharpPHard P ↔ PromisedCertificateSharpPHard P := by
  constructor
  · exact fun h f hf => h f hf.sharpP
  · exact fun h f hf => h f hf.certificateSharpP

theorem promisedSharpPHard_iff_singleTape (P : PromiseProblem) :
    PromisedSharpPHard P ↔ PromisedSingleTapeSharpPHard P := by
  constructor
  · exact fun h f hf => h f hf.sharpP
  · exact fun h f hf => h f hf.singleTapeSharpP

/-- Hardness propagates through the existing real oracle-subroutine compiler.
The composed witnesses retain every query promise and charge all answer bits. -/
theorem PromisedSharpPHard.trans {P Q : PromiseProblem} (h : PromisedSharpPHard P)
    (r : PromisePolyTimeTuringReduction P Q) : PromisedSharpPHard Q := by
  intro f hf
  obtain ⟨s⟩ := h f hf
  exact ⟨s.trans r⟩

/-- Exposing the uniformity in the definition: one machine works for every
extension, with legal queries and polynomial query-count/communication bounds. -/
theorem PromisedSharpPHard.uniform_machine {P : PromiseProblem} (h : PromisedSharpPHard P)
    (f : Bits → ℕ) (hf : SharpP f) :
    ∃ (m : OracleTM2) (p : Polynomial ℕ),
      ∀ oracle : Bits → Bits, (∀ q, P.valid q → oracle q=P.value q) →
      ∀ x, ∃ steps cost qs,
        m.Run oracle (m.initial x) (m.final (BitEncoding.nat.encode (f x))) steps cost qs ∧
        cost ≤ p.eval x.length ∧ qs.length ≤ p.eval x.length ∧
        ∀ q a, (q,a)∈qs → P.valid q ∧ q.length+a.length ≤ p.eval x.length := by
  obtain ⟨r⟩ := h f hf
  refine ⟨r.machine,r.time,fun oracle ho x => ?_⟩
  obtain ⟨steps,cost,qs,hr,hcost,hvalid⟩ := r.computes oracle ho x trivial
  exact ⟨steps,cost,qs,hr,hcost,hr.query_count_le.trans hcost,
    fun q a hqa => ⟨hvalid q a hqa,(hr.query_answer_length_le hqa).trans hcost⟩⟩

/-- Forgetting only the promise transcript yields hardness of every permitted
extension. This is one direction, not a replacement definition of promise hardness. -/
theorem PromisedSharpPHard.extension {P : PromiseProblem} (h : PromisedSharpPHard P)
    (oracle : Bits → Bits) (ho : ∀ q, P.valid q → oracle q=P.value q) : SharpPHard oracle := by
  intro f hf
  obtain ⟨r⟩ := h f hf
  refine ⟨{ machine := r.machine, time := r.time, computes := ?_ }⟩
  intro x
  obtain ⟨steps,cost,qs,hr,hcost,_⟩ := r.computes oracle ho x trivial
  exact ⟨steps,cost,qs,hr,hcost⟩

/-- Total binary oracles can be viewed as a promise with every word valid. -/
def totalOracleProblem (oracle : Bits → Bits) : PromiseProblem := ⟨fun _ => True, oracle⟩

/-- For total promises the new definition is exactly the existing hardness
notion, not a stronger source class or easier oracle convention. -/
theorem promisedSharpPHard_total_iff (oracle : Bits → Bits) :
    PromisedSharpPHard (totalOracleProblem oracle) ↔ SharpPHard oracle := by
  constructor
  · intro h
    exact h.extension oracle (fun _ _ => rfl)
  · intro h f hf
    obtain ⟨r⟩ := h f hf
    refine ⟨{ machine := r.machine, time := r.time, computes := ?_ }⟩
    intro oracle' ho x _
    have he : oracle'=oracle := funext (fun q => ho q trivial)
    subst oracle'
    obtain ⟨steps,cost,qs,hr,hcost⟩ := r.computes x
    exact ⟨steps,cost,qs,hr,hcost,fun _ _ _ => trivial⟩

/-- If a promised-hard problem has an actual promised polynomial-time solver,
every #P count has an actual solver on its original total raw input words. -/
theorem PromisedSharpPHard.counting_inFP {P : PromiseProblem} (h : PromisedSharpPHard P)
    (hP : P.InFP) (f : Bits → ℕ) (hf : SharpP f) : (countingProblem f).InFP := by
  obtain ⟨r⟩ := h f hf
  exact r.inFP hP

end PlanarHom.Complexity
