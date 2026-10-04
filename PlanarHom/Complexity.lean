import PlanarHom.Basic
import PlanarHom.MachineComposition
import Mathlib.Computability.TMComputable
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/-!
# Exact binary encodings and oracle TM2 computations

This file supplies concrete serialization and a bit-costed oracle extension of
mathlib's finite-control TM2 machines. It does not assert polynomial-time field
arithmetic, interpolation, machine composition, or a paper hardness theorem.
See `docs/SEMANTICS.md` for the computational model and its proved bridges.
-/

namespace PlanarHom.Complexity

abbrev Bits := List Bool

/-- An explicitly binary encoding, with a checked decoding round trip. -/
structure BitEncoding (α : Type) where
  encode : α → Bits
  decode : Bits → Option α
  decode_encode : ∀ a, decode (encode a) = some a

namespace BitEncoding

/-- Use the very same codewords in mathlib's machine-computability interface. -/
def toFinEncoding {α : Type} (e : BitEncoding α) : Computability.FinEncoding α where
  Γ := Bool
  encode := e.encode
  decode := e.decode
  decode_encode := e.decode_encode
  ΓFin := inferInstance

theorem injective {α : Type} (e : BitEncoding α) : Function.Injective e.encode :=
  e.toFinEncoding.toEncoding.encode_injective

/-- Raw bit strings do not receive a second layer of encoding. -/
def bits : BitEncoding Bits := ⟨id, some, fun _ => rfl⟩

/-- Little-endian binary natural numbers, as supplied by mathlib. -/
def nat : BitEncoding ℕ where
  encode := Computability.encodeNat
  decode s := some (Computability.decodeNat s)
  decode_encode n := congrArg some (Computability.decode_encodeNat n)

/-- Unary size data, used for the number of explicitly present graph vertices.
Binary vertex counts alone would succinctly encode exponentially many isolated vertices. -/
def unaryNat : BitEncoding ℕ where
  encode := Computability.unaryEncodeNat
  decode s := some s.length
  decode_encode n := congrArg some (Computability.unary_decode_encode_nat n)

@[simp] theorem unaryNat_length (n : ℕ) : (unaryNat.encode n).length = n :=
  Computability.unary_decode_encode_nat n

/-- A bit is a single bit, not a unary natural. -/
def bool : BitEncoding Bool where
  encode b := [b]
  decode
    | [b] => some b
    | _ => none
  decode_encode _ := rfl

/-- Escape a word: every data bit is preceded by `true`, then `false` ends it. -/
def frame : Bits → Bits
  | [] => [false]
  | b :: bs => true :: b :: frame bs

/-- Read one escaped word and return its unconsumed suffix. -/
def unframe : Bits → Option (Bits × Bits)
  | false :: bs => some ([], bs)
  | true :: b :: bs => do
      let (word, rest) ← unframe bs
      return (b :: word, rest)
  | _ => none

@[simp] theorem unframe_frame_append (a b : Bits) :
    unframe (frame a ++ b) = some (a, b) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [frame, unframe, ih]

@[simp] theorem frame_length (a : Bits) : (frame a).length = 2 * a.length + 1 := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [frame, ih]; omega

/-- A product is one framed first codeword followed by the second codeword. -/
def prod {α β : Type} (a : BitEncoding α) (b : BitEncoding β) :
    BitEncoding (α × β) where
  encode x := frame (a.encode x.1) ++ b.encode x.2
  decode s := do
    let (sa, sb) ← unframe s
    let xa ← a.decode sa
    let xb ← b.decode sb
    return (xa, xb)
  decode_encode x := by simp [unframe_frame_append, a.decode_encode, b.decode_encode]

@[simp] theorem prod_length {α β : Type} (a : BitEncoding α) (b : BitEncoding β)
    (x : α × β) :
    ((a.prod b).encode x).length = 2 * (a.encode x.1).length +
      (b.encode x.2).length + 1 := by
  simp [prod]; omega

/-- A sequence of individually framed words, without its length header. -/
def frames : List Bits → Bits
  | [] => []
  | w :: ws => frame w ++ frames ws

/-- Escaping costs two bits per payload bit and one delimiter per word. -/
theorem frames_length (ws : List Bits) :
    (frames ws).length = 2 * (ws.map List.length).sum + ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [frames, ih]; omega

/-- Parse a specified finite number of words. The fuel is the encoded length. -/
def unframes : ℕ → Bits → Option (List Bits × Bits)
  | 0, s => some ([], s)
  | n + 1, s => do
      let (w, rest) ← unframe s
      let (ws, tail) ← unframes n rest
      return (w :: ws, tail)

@[simp] theorem unframes_frames_append (ws : List Bits) (tail : Bits) :
    unframes ws.length (frames ws ++ tail) = some (ws, tail) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [frames, unframes, List.append_assoc, ih]

@[simp] theorem unframes_frames (ws : List Bits) :
    unframes ws.length (frames ws) = some (ws, []) := by
  simpa using unframes_frames_append ws []

/-- Lists carry a binary length header; arbitrary long payloads are never atoms. -/
def list {α : Type} (a : BitEncoding α) : BitEncoding (List α) where
  encode xs := frame (nat.encode xs.length) ++ frames (xs.map a.encode)
  decode s := do
    let (size, rest) ← unframe s
    let n ← nat.decode size
    let (words, tail) ← unframes n rest
    if tail = [] then words.mapM a.decode else none
  decode_encode xs := by
    have hm : (xs.map a.encode).mapM a.decode = some xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [List.map_cons, List.mapM_cons, a.decode_encode, ih]
    have h : unframes xs.length (frames (xs.map a.encode)) =
        some (xs.map a.encode, []) := by simpa using unframes_frames (xs.map a.encode)
    simpa [nat, h] using hm

/-- An explicit occurrence list cannot hide more items than its bit length. -/
theorem list_length_le {α : Type} (e : BitEncoding α) (xs : List α) :
    xs.length ≤ (e.list.encode xs).length := by
  simp only [list, List.length_append, frame_length, frames_length, List.length_map]
  omega

/-- A fixed coordinate vector is encoded as a list with its required length checked. -/
def vector {α : Type} (e : BitEncoding α) (n : ℕ) : BitEncoding (Fin n → α) where
  encode f := e.list.encode (List.ofFn f)
  decode s := do
    let xs ← e.list.decode s
    if h : xs.length = n then
      some (fun i => xs[i.val]'(by omega))
    else none
  decode_encode f := by simp [e.list.decode_encode]

/-- Transport an encoding along a concrete retract. No efficiency is asserted. -/
def retract {α β : Type} (e : BitEncoding β) (f : α → β) (g : β → α)
    (h : ∀ a, g (f a) = a) : BitEncoding α where
  encode a := e.encode (f a)
  decode s := (e.decode s).map g
  decode_encode a := by rw [e.decode_encode]; simp [h]

/-- Signed binary integers, using the two constructors of `Int`. -/
def int : BitEncoding ℤ :=
  (bool.prod nat).retract
    (fun z => match z with
      | .ofNat n => (false, n)
      | .negSucc n => (true, n))
    (fun p => if p.1 then Int.negSucc p.2 else Int.ofNat p.2)
    (by intro z; cases z <;> rfl)

/-- Exact rationals are encoded by their reduced numerator and positive denominator.
The decoder normalizes even noncanonical input pairs. -/
def rat : BitEncoding ℚ :=
  (int.prod nat).retract (fun q => (q.num, q.den))
    (fun p => mkRat p.1 p.2) Rat.mkRat_self

end BitEncoding

/-- Explicit edge occurrences preserve parallel edges and self-loops. Endpoint
validity and planarity are separate promises, not silently assumed by the codec. -/
structure GraphCode where
  vertices : ℕ
  edges : List (ℕ × ℕ)
  deriving DecidableEq

namespace GraphCode

/-- An occurrence list uses vertex indices in `0, …, vertices - 1`. -/
def Valid (g : GraphCode) : Prop :=
  ∀ e ∈ g.edges, e.1 < g.vertices ∧ e.2 < g.vertices

/-- Interpret the serialized occurrence list in the project's finite multigraph
semantics. Each occurrence has its own edge index, even for parallel edges. -/
def toMultiGraph (g : GraphCode) (valid : g.Valid) :
    PlanarHom.MultiGraph (Fin g.vertices) (Fin g.edges.length) where
  src e := ⟨(g.edges.get e).1, (valid _ (List.get_mem _ _)).1⟩
  dst e := ⟨(g.edges.get e).2, (valid _ (List.get_mem _ _)).2⟩

/-- Exact evaluation of a valid code uses precisely the already-proved finite
assignment-sum semantics. This definition claims no algorithm or planarity. -/
noncomputable def evaluate {C R : Type} [Fintype C] [CommSemiring R]
    (g : GraphCode) (valid : g.Valid) (interaction : Matrix C C R) (weights : C → R) : R :=
  (g.toMultiGraph valid).partition interaction weights

/-- Unary vertex count and binary ordered edge occurrences. In particular,
isolated vertices are not compressed into a logarithmic-size graph description. -/
def encoding : BitEncoding GraphCode :=
  (BitEncoding.unaryNat.prod (BitEncoding.nat.prod BitEncoding.nat).list).retract
    (fun g => (g.vertices, g.edges)) (fun p => ⟨p.1, p.2⟩)
    (by intro g; cases g; rfl)

/-- Every vertex, including an isolated vertex, is charged in the input length. -/
theorem vertices_le_length (g : GraphCode) : g.vertices ≤ (encoding.encode g).length := by
  simp only [encoding, BitEncoding.retract, BitEncoding.prod_length,
    BitEncoding.unaryNat_length]
  omega

/-- Input bit length bounds vertices plus edge occurrences, including multiplicity. -/
theorem size_le_length (g : GraphCode) :
    g.vertices + g.edges.length ≤ (encoding.encode g).length := by
  have h := (BitEncoding.nat.prod BitEncoding.nat).list_length_le g.edges
  simp only [encoding, BitEncoding.retract, BitEncoding.prod_length,
    BitEncoding.unaryNat_length]
  omega

end GraphCode

/-- Raw finite-language input. Each edge has two endpoint indices and one binary
label index; each unary occurrence has one vertex index and one unary label index.
The two numbers of label types are fixed parameters of `Valid`, not variable weights. -/
structure MixedCode where
  vertices : ℕ
  edges : List (ℕ × (ℕ × ℕ))
  unaries : List (ℕ × ℕ)
  deriving DecidableEq

namespace MixedCode

def Valid (binaryTypes unaryTypes : ℕ) (g : MixedCode) : Prop :=
  (∀ e ∈ g.edges, e.1 < g.vertices ∧ e.2.1 < g.vertices ∧ e.2.2 < binaryTypes) ∧
  (∀ u ∈ g.unaries, u.1 < g.vertices ∧ u.2 < unaryTypes)

def encoding : BitEncoding MixedCode :=
  (BitEncoding.unaryNat.prod
    (((BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)).list).prod
      (BitEncoding.nat.prod BitEncoding.nat).list)).retract
    (fun g => (g.vertices, (g.edges, g.unaries)))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (by intro g; cases g; rfl)

end MixedCode

/-- Fixed-number-field outputs will be a fixed number of exact rational
coordinates. This codec deliberately makes no field-arithmetic complexity claim. -/
def rationalCoordinates (dimension : ℕ) : BitEncoding (Fin dimension → ℚ) :=
  BitEncoding.rat.vector dimension

/-- The fixed-basis representation of a number-field value. Coefficients are
serialized as reduced binary rationals and decode to the exact field element.
Choosing a basis is fixed problem data; this is not an arithmetic algorithm. -/
noncomputable def numberFieldEncoding {K : Type} [Field K] [Algebra ℚ K]
    {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K) : BitEncoding K :=
  (rationalCoordinates dimension).retract basis.equivFun basis.equivFun.symm
    basis.equivFun.symm_apply_apply

/-- Genuine mathlib TM2 polynomial-time computability for the supplied bit codes.
This is an existential over machines and proofs, not an uninterpreted predicate. -/
def FP {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) (f : α → β) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding f)

theorem fp_id {α : Type} (e : BitEncoding α) : FP e e id :=
  ⟨Turing.idComputableInPolyTime e.toFinEncoding⟩

/-- Ordinary polynomial-time computability is closed under composition by the
project's proved typed TM2 compiler, not the unfinished mathlib declaration. -/
theorem FP.comp {α β γ : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    {ec : BitEncoding γ} {f : α → β} {g : β → γ}
    (hf : FP ea eb f) (hg : FP eb ec g) : FP ea ec (g ∘ f) := by
  obtain ⟨mf⟩ := hf
  obtain ⟨mg⟩ := hg
  exact ⟨PlanarHom.MachineComposition.composeComputers mf mg⟩

/-- An oracle extension of a genuine TM2 program. Every stack alphabet is finite;
all ordinary operations are the fixed program's TM2 instructions. A query label
only specifies a continuation label, never an arbitrary data-processing function. -/
structure OracleTM2 where
  core : Turing.TM2ComputableAux Bool Bool
  finiteAlphabet : ∀ k, Fintype (core.tm.Γ k)
  queryStack : core.tm.K
  answerStack : core.tm.K
  queryAlphabet : core.tm.Γ queryStack ≃ Bool
  answerAlphabet : core.tm.Γ answerStack ≃ Bool
  request : core.tm.Λ → Option core.tm.Λ

namespace OracleTM2

abbrev Cfg (m : OracleTM2) := m.core.tm.Cfg

/-- Query words are materialized bit strings on a designated stack. -/
def queryWord (m : OracleTM2) (c : m.Cfg) : Bits :=
  (c.stk m.queryStack).map m.queryAlphabet

/-- Query instructions are finite-control labels. A halted configuration cannot query. -/
def continuation (m : OracleTM2) (c : m.Cfg) : Option m.core.tm.Λ :=
  c.l.bind m.request

/-- Install the exact oracle answer and resume at the declared label. The answer
length is explicitly charged by `Run`, even though installation is one oracle step. -/
def answerCfg (m : OracleTM2) (oracle : Bits → Bits) (c : m.Cfg)
    (next : m.core.tm.Λ) : m.Cfg where
  l := some next
  var := c.var
  stk := Function.update c.stk m.answerStack
    ((oracle (m.queryWord c)).map m.answerAlphabet.symm)

/-- The ordinary transition is literally the transition of the underlying TM2. -/
def step (m : OracleTM2) (oracle : Bits → Bits) (c : m.Cfg) : Option m.Cfg :=
  match m.continuation c with
  | none => m.core.tm.step c
  | some next => some (m.answerCfg oracle c next)

/-- The input convention is exactly mathlib's `initList`. -/
def initial (m : OracleTM2) (x : Bits) : m.Cfg :=
  Turing.initList m.core.tm (x.map m.core.inputAlphabet.symm)

/-- The output convention is exactly mathlib's `haltList`. Other stacks must
be cleared and the finite internal state reset, as required by that interface. -/
def final (m : OracleTM2) (y : Bits) : m.Cfg :=
  Turing.haltList m.core.tm (y.map m.core.outputAlphabet.symm)

/-- A transcript records every actual query and its complete exact answer. -/
abbrev Transcript := List (Bits × Bits)

/-- Total number of oracle-interface bits appearing in a transcript. -/
def transcriptBits (qs : Transcript) : ℕ :=
  (qs.map (fun qa => qa.1.length + qa.2.length)).sum

/-- A finite run records the number of machine transitions, charged bit cost,
and ordered transcript. An ordinary TM2 transition costs one; a query additionally
costs the complete query and answer lengths. There is no free arithmetic primitive. -/
inductive Run (m : OracleTM2) (oracle : Bits → Bits) :
    m.Cfg → m.Cfg → ℕ → ℕ → Transcript → Prop
  | refl (c) : Run m oracle c c 0 0 []
  | ordinary {c d e steps cost qs}
      (notQuery : m.continuation c = none)
      (transition : m.core.tm.step c = some d)
      (rest : Run m oracle d e steps cost qs) :
      Run m oracle c e (steps + 1) (cost + 1) qs
  | query {c e steps cost qs} (next)
      (isQuery : m.continuation c = some next)
      (rest : Run m oracle (m.answerCfg oracle c next) e steps cost qs) :
      Run m oracle c e (steps + 1)
        (cost + 1 + (m.queryWord c).length + (oracle (m.queryWord c)).length)
        ((m.queryWord c, oracle (m.queryWord c)) :: qs)

namespace Run

variable {m : OracleTM2} {oracle : Bits → Bits} {c d : m.Cfg}
variable {steps cost : ℕ} {qs : Transcript}

/-- Charged time is exactly transition time plus oracle communication size. -/
theorem cost_eq (h : m.Run oracle c d steps cost qs) :
    cost = steps + transcriptBits qs := by
  induction h with
  | refl => rfl
  | ordinary _ _ _ ih => simp_all [transcriptBits]; omega
  | query _ _ _ ih => simp_all [transcriptBits]; omega

/-- No execution can hide superpolynomially many transitions in the cost bound. -/
theorem steps_le (h : m.Run oracle c d steps cost qs) : steps ≤ cost := by
  rw [h.cost_eq]
  exact Nat.le_add_right _ _

/-- The number of oracle calls is bounded by the charged execution time. -/
theorem query_count_le_steps (h : m.Run oracle c d steps cost qs) : qs.length ≤ steps := by
  induction h with
  | refl => rfl
  | ordinary _ _ _ ih => exact Nat.le_trans ih (Nat.le_succ _)
  | query _ _ _ ih => simpa using Nat.succ_le_succ ih

theorem query_count_le (h : m.Run oracle c d steps cost qs) : qs.length ≤ cost :=
  h.query_count_le_steps.trans h.steps_le

/-- All query and answer bits together fit in the charged execution time. -/
theorem transcriptBits_le (h : m.Run oracle c d steps cost qs) : transcriptBits qs ≤ cost := by
  rw [h.cost_eq]
  exact Nat.le_add_left _ _

/-- In particular, every individual query and exact answer have bounded bit length. -/
theorem query_answer_length_le (h : m.Run oracle c d steps cost qs)
    {q a : Bits} (hqa : (q, a) ∈ qs) : q.length + a.length ≤ cost := by
  have hs : q.length + a.length ≤ transcriptBits qs :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _
      (List.mem_map.mpr ⟨(q, a), hqa, rfl⟩)
  exact hs.trans h.transcriptBits_le

/-- Erasing communication charges preserves exactly the recorded transitions. -/
theorem evalsInSteps (h : m.Run oracle c d steps cost qs) :
    (flip Option.bind (m.step oracle))^[steps] (some c) = some d := by
  induction h with
  | refl => rfl
  | @ordinary c d e steps cost qs hn ht hr ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind (m.step oracle))^[steps] (m.step oracle c) = some e
      rw [step, hn, ht]
      exact ih
  | @query c e steps cost qs next hq hr ih =>
      simpa [Function.iterate_succ_apply, flip, step, hq] using ih

/-- A charged run yields mathlib's actual bounded-iteration witness. -/
def evalsToInTime (h : m.Run oracle c d steps cost qs) :
    Turing.EvalsToInTime (m.step oracle) c (some d) cost :=
  ⟨⟨steps, h.evalsInSteps⟩, h.steps_le⟩

/-- Finite execution segments compose with additive cost and concatenated transcripts.
Machine-level polynomial-time composition is established separately. -/
theorem trans {e : m.Cfg} {s₂ t₂ : ℕ} {qs₂ : Transcript}
    (h₁ : m.Run oracle c d steps cost qs) (h₂ : m.Run oracle d e s₂ t₂ qs₂) :
    m.Run oracle c e (steps + s₂) (cost + t₂) (qs ++ qs₂) := by
  induction h₁ with
  | refl => simpa using h₂
  | ordinary hn ht hr ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Run.ordinary hn ht (ih h₂)
  | query next hq hr ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Run.query next hq (ih h₂)

end Run

/-- Disabling all request labels recovers the underlying TM2 step, definitionally
on every ordinary instruction. This prevents a unit-cost host-language gap. -/
theorem step_eq_of_no_queries (m : OracleTM2) (h : ∀ l, m.request l = none)
    (oracle : Bits → Bits) : m.step oracle = m.core.tm.step := by
  funext c
  have hc : m.continuation c = none := by
    cases he : c.l <;> simp [continuation, he, h]
  simp [step, hc]

/-- Query-free runs use mathlib's original exact input/output and time conventions. -/
def outputsInTime_of_no_queries (m : OracleTM2) (h : ∀ l, m.request l = none)
    {oracle : Bits → Bits} {x y : Bits} {steps cost : ℕ} {qs : Transcript}
    (run : m.Run oracle (m.initial x) (m.final y) steps cost qs) :
    Turing.TM2OutputsInTime m.core.tm (x.map m.core.inputAlphabet.symm)
      (some (y.map m.core.outputAlphabet.symm)) cost := by
  have ht := run.evalsToInTime
  rw [m.step_eq_of_no_queries h oracle] at ht
  exact ht

end OracleTM2

/-- An exact polynomial-time Turing reduction on binary strings in the charged
oracle-TM2 model. It records real machine executions and bounds all query and
answer lengths, rather than counting arbitrary host-language functions as steps. -/
structure PolyTimeTuringReduction (target oracle : Bits → Bits) where
  machine : OracleTM2
  time : Polynomial ℕ
  computes : ∀ x, ∃ steps cost qs,
    machine.Run oracle (machine.initial x) (machine.final (target x)) steps cost qs ∧
    cost ≤ time.eval x.length

namespace PolyTimeTuringReduction

/-- With no query labels, the reduction is an actual polynomial-time computer in
mathlib's original model, with the same binary codewords and polynomial bound. -/
noncomputable def toComputerOfNoQueries {target oracle : Bits → Bits}
    (r : PolyTimeTuringReduction target oracle)
    (h : ∀ l, r.machine.request l = none) :
    Turing.TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding
      BitEncoding.bits.toFinEncoding target where
  toTM2ComputableAux := r.machine.core
  time := r.time
  outputsFun x := Classical.choice (by
    obtain ⟨steps, cost, qs, hr, ht⟩ := r.computes x
    have out := r.machine.outputsInTime_of_no_queries h hr
    exact ⟨⟨out.toEvalsTo, out.steps_le_m.trans ht⟩⟩)

theorem fp_of_no_queries {target oracle : Bits → Bits}
    (r : PolyTimeTuringReduction target oracle)
    (h : ∀ l, r.machine.request l = none) :
    FP BitEncoding.bits BitEncoding.bits target :=
  ⟨r.toComputerOfNoQueries h⟩

/-- Every reduction's queried words and answers satisfy its polynomial bit bound. -/
theorem query_bound {target oracle : Bits → Bits}
    (r : PolyTimeTuringReduction target oracle) (x : Bits) :
    ∃ steps cost qs,
      r.machine.Run oracle (r.machine.initial x) (r.machine.final (target x)) steps cost qs ∧
      qs.length ≤ r.time.eval x.length ∧
      ∀ q a, (q, a) ∈ qs → q.length + a.length ≤ r.time.eval x.length := by
  obtain ⟨steps, cost, qs, hr, ht⟩ := r.computes x
  exact ⟨steps, cost, qs, hr, hr.query_count_le.trans ht,
    fun _ _ hqa => (hr.query_answer_length_le hqa).trans ht⟩

end PolyTimeTuringReduction

/-- A proposition-valued reduction relation whose witnesses are concrete machines. -/
def TuringReduces (target oracle : Bits → Bits) : Prop :=
  Nonempty (PolyTimeTuringReduction target oracle)

/-- A minimal concrete oracle machine: query the input once, then halt with the
answer on its input/output stack. All alphabets and control sets are explicitly finite. -/
def directQueryMachine : OracleTM2 where
  core := {
    tm := {
      K := Unit
      k₀ := ()
      k₁ := ()
      Γ := fun _ => Bool
      Λ := Bool
      main := false
      σ := Unit
      initialState := ()
      Γk₀Fin := inferInstance
      m := fun _ => Turing.TM2.Stmt.halt }
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool }
  finiteAlphabet := fun _ => inferInstance
  queryStack := ()
  answerStack := ()
  queryAlphabet := Equiv.refl Bool
  answerAlphabet := Equiv.refl Bool
  request := fun l => if l then none else some true

/-- The direct query machine has a verified two-transition execution, and charges
the entire oracle output. This is a concrete test of the oracle semantics. -/
theorem directQueryMachine_run (oracle : Bits → Bits) (x : Bits) :
    directQueryMachine.Run oracle (directQueryMachine.initial x)
      (directQueryMachine.final (oracle x)) 2 (2 + x.length + (oracle x).length)
      [(x, oracle x)] := by
  have hq : directQueryMachine.continuation (directQueryMachine.initial x) = some true := rfl
  have hn : directQueryMachine.continuation
      (directQueryMachine.answerCfg oracle (directQueryMachine.initial x) true) = none := rfl
  have hw : directQueryMachine.queryWord (directQueryMachine.initial x) = x := by
    simp [OracleTM2.queryWord, OracleTM2.initial, Turing.initList, directQueryMachine]
  have hs : directQueryMachine.core.tm.step
      (directQueryMachine.answerCfg oracle (directQueryMachine.initial x) true) =
      some (directQueryMachine.final (oracle x)) := by
    simp [Turing.FinTM2.step, OracleTM2.answerCfg, OracleTM2.final, directQueryMachine,
      Turing.TM2.step, Turing.TM2.stepAux, Turing.haltList,
      OracleTM2.initial, OracleTM2.queryWord, Turing.initList]
    funext k
    cases k
    simp
  simpa [hw, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    OracleTM2.Run.query true hq
      (OracleTM2.Run.ordinary hn hs (OracleTM2.Run.refl _))

/-- Reflexivity is available for polynomial-output-size oracles. Charging the
answer makes this hypothesis explicit instead of silently allowing enormous outputs. -/
noncomputable def directQueryReduction (oracle : Bits → Bits) (p : Polynomial ℕ)
    (sizeBound : ∀ x, (oracle x).length ≤ p.eval x.length) :
    PolyTimeTuringReduction oracle oracle where
  machine := directQueryMachine
  time := 2 + Polynomial.X + p
  computes x := by
    refine ⟨2, 2 + x.length + (oracle x).length, [(x, oracle x)],
      directQueryMachine_run oracle x, ?_⟩
    simpa using Nat.add_le_add_left (sizeBound x) (2 + x.length)

/-- A promise separates syntactic input validity and the permitted graph class
from the exact value. No planarity algorithm is silently assumed. -/
structure PromiseProblem where
  valid : Bits → Prop
  value : Bits → Bits

/-- A promised reduction must query only source-valid strings and work against
every extension of the promised oracle. Invalid oracle values cannot act as advice. -/
structure PromisePolyTimeTuringReduction (target source : PromiseProblem) where
  machine : OracleTM2
  time : Polynomial ℕ
  computes : ∀ oracle : Bits → Bits,
    (∀ q, source.valid q → oracle q = source.value q) →
    ∀ x, target.valid x → ∃ steps cost qs,
      machine.Run oracle (machine.initial x) (machine.final (target.value x)) steps cost qs ∧
      cost ≤ time.eval x.length ∧ ∀ q a, (q, a) ∈ qs → source.valid q

/-- The concrete certificate-counting form of a counting computation: there are
exactly `p(length x)` binary choices and a deterministic binary verifier. -/
noncomputable def certificateCount (p : Polynomial ℕ) (verifier : Bits × Bits → Bool)
    (x : Bits) : ℕ :=
  Fintype.card {w : Fin (p.eval x.length) → Bool // verifier (x, List.ofFn w) = true}

/-- A machine-based certificate-counting class. A proof of equivalence with an
independently defined nondeterministic-TM #P class is not supplied here. -/
def CertificateSharpP (f : Bits → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∃ verifier : Bits × Bits → Bool,
    FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool verifier ∧
    ∀ x, f x = certificateCount p verifier x

/-- Hardness for the explicitly defined certificate-counting class. This does not
silently assume the missing nondeterministic-machine equivalence or any hard endpoint. -/
def CertificateSharpPHard (oracle : Bits → Bits) : Prop :=
  ∀ f : Bits → ℕ, CertificateSharpP f →
    TuringReduces (fun x => BitEncoding.nat.encode (f x)) oracle

/-- A decoded function becomes a total exact binary oracle. Malformed input is
sent to a fixed, explicit output; promise restrictions must be tracked separately. -/
def encodedFunction {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β)
    (f : α → β) (invalid : Bits) (x : Bits) : Bits :=
  match ea.decode x with
  | some a => eb.encode (f a)
  | none => invalid

@[simp] theorem encodedFunction_encode {α β : Type} (ea : BitEncoding α)
    (eb : BitEncoding β) (f : α → β) (invalid : Bits) (a : α) :
    encodedFunction ea eb f invalid (ea.encode a) = eb.encode (f a) := by
  simp [encodedFunction, ea.decode_encode]

end PlanarHom.Complexity
