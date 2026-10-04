import PlanarHom.SingleTapeNondeterministic
import PlanarHom.TapeMirrorCompiler

/-! # Local input loading for the mirrored multistack simulator

Raw bits have separate tags, so a final `false` is never confused with blank.
The rightmost input cell carries the common bottom marker: mathlib overlays
that marker on the first track cell, rather than inserting a new stack cell.
-/
namespace PlanarHom.TM2SingleTapeLoading
open Turing SingleTapeNondeterministic

variable {K : Type} {Γ : K → Type}

inductive Alphabet (K : Type) (Γ : K → Type) where
  | raw (bit : Bool)
  | sim (symbol : TM2to1.Γ' K Γ)

instance : Inhabited (Alphabet K Γ) := ⟨.sim default⟩

instance [DecidableEq K] [Fintype K] [∀ k, Fintype (Γ k)] :
    Fintype (Alphabet K Γ) :=
  Fintype.ofEquiv (Bool ⊕ TM2to1.Γ' K Γ)
    ⟨(fun x => match x with | .inl b => .raw b | .inr a => .sim a),
     (fun x => match x with | .raw b => .inl b | .sim a => .inr a),
     (by intro x; cases x <;> rfl), (by intro x; cases x <;> rfl)⟩

def embedding : PointedMap (TM2to1.Γ' K Γ) (Alphabet K Γ) := ⟨.sim, rfl⟩

@[simp] theorem raw_injective : Function.Injective (Alphabet.raw (K := K) (Γ := Γ)) :=
  fun _ _ h => Alphabet.raw.inj h

@[simp] theorem raw_ne_blank (b : Bool) : Alphabet.raw (K := K) (Γ := Γ) b ≠ default :=
  fun h => Alphabet.noConfusion h

/-- Applying a genuine single-tape local action. This is definitionally the
operation used by `SingleTapeNondeterministic.Machine.execute`. -/
def execute {A Q : Type} [Inhabited A] (a : Action A Q) (t : Tape A) : Control Q × Tape A :=
  (a.next, match a.motion with
    | .stay => t.write a.write
    | .left => (t.write a.write).move .left
    | .right => (t.write a.write).move .right)

def mapControl {Q R : Type} (f : Q → R) : Control Q → Control R
  | .run q => .run (f q)
  | .accept => .accept
  | .reject => .reject

/-- Embed local program states into any enclosing compiler's finite control. -/
def mapAction {A Q R : Type} (f : Q → R) (a : Action A Q) : Action A R :=
  { a with next := mapControl f a.next }

theorem execute_mapAction {A Q R : Type} [Inhabited A] (f : Q → R)
    (a : Action A Q) (t : Tape A) :
    execute (mapAction f a) t = Prod.map (mapControl f) id (execute a t) := rfl

def mirrorMotion : Motion → Motion
  | .stay => .stay
  | .left => .right
  | .right => .left

def transport {A B : Type} [Inhabited A] [Inhabited B]
    (e : PointedMap A B) (t : Tape A) : Tape B :=
  (TapeMirrorCompiler.mirror t).map e

/-- Transport an ordinary primitive instruction by alphabet and control maps,
reversing its local motion to match the mirrored representation. -/
def mirroredAction {A B Q R : Type} [Inhabited A] [Inhabited B]
    (e : PointedMap A B) (f : Q → R) (a : Action A Q) : Action B R :=
  ⟨e a.write, mirrorMotion a.motion, mapControl f a.next⟩

theorem execute_mirroredAction {A B Q R : Type} [Inhabited A] [Inhabited B]
    (e : PointedMap A B) (f : Q → R) (a : Action A Q) (t : Tape A) :
    execute (mirroredAction e f a) (transport e t) =
      Prod.map (mapControl f) (transport e) (execute a t) := by
  rcases a with ⟨a, d, q⟩
  cases d <;>
    simp only [execute, mirroredAction, mirrorMotion, transport, Prod.map,
      TapeMirrorCompiler.mirror_write, TapeMirrorCompiler.mirror_move,
      TapeMirrorCompiler.direction, Tape.map_write, Tape.map_move]

/-- The control map may also redirect a simulator halt into a local checker. -/
def mirroredActionWith {A B Q R : Type} [Inhabited A] [Inhabited B]
    (e : PointedMap A B) (f : Control Q → Control R) (a : Action A Q) : Action B R :=
  ⟨e a.write, mirrorMotion a.motion, f a.next⟩

theorem execute_mirroredActionWith {A B Q R : Type} [Inhabited A] [Inhabited B]
    (e : PointedMap A B) (f : Control Q → Control R) (a : Action A Q) (t : Tape A) :
    execute (mirroredActionWith e f a) (transport e t) =
      Prod.map f (transport e) (execute a t) := by
  rcases a with ⟨a, d, q⟩
  cases d <;>
    simp only [execute, mirroredActionWith, mirrorMotion, transport, Prod.map,
      TapeMirrorCompiler.mirror_write, TapeMirrorCompiler.mirror_move,
      TapeMirrorCompiler.direction, Tape.map_write, Tape.map_move]

inductive LoaderState where
  | scan (seen : Bool)
  | mark
  | done
  deriving DecidableEq, Fintype

variable [DecidableEq K] (k : K) (encode : Bool → Γ k)

def tracks (b : Bool) : ∀ j, Option (Γ j) :=
  Function.update (fun _ => none) k (some (encode b))

def converted (b : Bool) : Alphabet K Γ := .sim (false, tracks k encode b)

def loaderAction : LoaderState → Alphabet K Γ → Action (Alphabet K Γ) LoaderState
  | .scan _, .raw b => ⟨converted k encode b, .right, .run (.scan true)⟩
  | .scan false, .sim _ => ⟨.sim (true, fun _ => none), .stay, .run .done⟩
  | .scan true, a => ⟨a, .left, .run .mark⟩
  | .mark, .sim a => ⟨.sim (true, a.2), .stay, .run .done⟩
  | .mark, a => ⟨a, .stay, .reject⟩
  | .done, a => ⟨a, .stay, .accept⟩

def loaderStep : Control LoaderState × Tape (Alphabet K Γ) →
    Control LoaderState × Tape (Alphabet K Γ)
  | (.run q, t) => execute (loaderAction k encode q t.head) t
  | c => c

def loaded (x : List Bool) : Tape (Alphabet K Γ) :=
  TapeMirrorCompiler.mirror
    ((Tape.mk₁ (TM2to1.trInit k (x.map encode))).map embedding)

theorem loaded_transport (x : List Bool) :
    loaded k encode x = transport embedding (Tape.mk₁ (TM2to1.trInit k (x.map encode))) := rfl

@[simp] theorem loader_raw (seen : Bool) (b : Bool) (xs : List Bool)
    (left : List (Alphabet K Γ)) :
    loaderStep k encode (.run (.scan seen), Tape.mk₂ left ((b :: xs).map .raw)) =
      (.run (.scan true), Tape.mk₂ (converted k encode b :: left) (xs.map .raw)) := by
  cases seen <;> rfl

/-- Every raw cell costs one actual write-and-move transition. -/
theorem scan_true (xs : List Bool) (left : List (Alphabet K Γ)) :
    (loaderStep k encode)^[xs.length]
      (.run (.scan true), Tape.mk₂ left (xs.map .raw)) =
    (.run (.scan true), Tape.mk₂ (xs.reverse.map (converted k encode) ++ left) []) := by
  induction xs generalizing left with
  | nil => rfl
  | cons b xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply, loader_raw, ih]
    simp only [List.reverse_cons, List.map_append, List.map_singleton, List.append_assoc,
      List.singleton_append]

omit [DecidableEq K] in
private theorem blank_singleton :
    ListBlank.mk [(default : Alphabet K Γ)] = ListBlank.mk [] :=
  Quotient.sound' (Or.inr ⟨1, rfl⟩)

theorem loaded_nil : loaded k encode [] =
    ⟨.sim (true, fun _ => none), ListBlank.mk [], ListBlank.mk []⟩ := rfl

theorem loaded_of_reverse (xs : List Bool) (b : Bool) (bs : List Bool)
    (h : xs.reverse = b :: bs) :
    loaded k encode xs =
      ⟨.sim (true, tracks k encode b), ListBlank.mk (bs.map (converted k encode)),
       ListBlank.mk []⟩ := by
  simp only [loaded, TM2to1.trInit, ← List.map_reverse, h, List.map_cons, List.headI_cons,
    List.tail_cons, Tape.mk₁, Tape.mk₂, Tape.mk', Tape.map, TapeMirrorCompiler.mirror,
    ListBlank.head_mk, ListBlank.tail_mk, ListBlank.map_mk, List.map_nil,
    List.map_cons, List.map_map]
  rfl

/-- In particular a trailing false remains an actual `some` symbol on the input
track at the marked bottom; it is never discarded as a blank. -/
theorem loaded_append_bit (xs : List Bool) (b : Bool) :
    loaded k encode (xs ++ [b]) =
      ⟨.sim (true, tracks k encode b), ListBlank.mk (xs.reverse.map (converted k encode)),
       ListBlank.mk []⟩ :=
  loaded_of_reverse k encode _ b xs.reverse (by simp)

theorem finish_nonempty (xs : List Bool) (h : xs ≠ []) :
    (loaderStep k encode)^[2]
      (.run (.scan true), Tape.mk₂ (xs.reverse.map (converted k encode)) []) =
      (.run .done, loaded k encode xs) := by
  obtain ⟨b, bs, he⟩ := List.exists_cons_of_ne_nil
    (show xs.reverse ≠ [] by simpa using h)
  rw [loaded_of_reverse k encode xs b bs he, he]
  change (Control.run LoaderState.done,
    (⟨.sim (true, tracks k encode b),
      ListBlank.mk (bs.map (converted k encode)), ListBlank.mk [default]⟩ :
        Tape (Alphabet K Γ))) = _
  rw [blank_singleton]

/-- The empty input takes one transition; every nonempty input takes `n+2`.
The result is exactly mathlib's initial parallel-track tape with orientation
reversed and the simulator alphabet embedded, not an assumed tape reversal. -/
theorem loader_exact (xs : List Bool) :
    (loaderStep k encode)^[if xs = [] then 1 else xs.length + 2]
      (.run (.scan false), Tape.mk₁ (xs.map .raw)) =
      (.run .done, loaded k encode xs) := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    simp only [reduceCtorEq, if_false, List.length_cons]
    rw [show xs.length + 1 + 2 = (xs.length + 2) + 1 by omega,
      Function.iterate_succ_apply]
    change (loaderStep k encode)^[xs.length + 2]
      (.run (.scan true), Tape.mk₂ [converted k encode b] (xs.map .raw)) = _
    rw [Nat.add_comm xs.length 2, Function.iterate_add_apply, scan_true]
    have hp : xs.reverse.map (converted k encode) ++ [converted k encode b] =
        (b :: xs).reverse.map (converted k encode) := by simp
    rw [hp]
    exact finish_nonempty k encode (b :: xs) (by simp)

def loaderMachine [Fintype K] [∀ j, Fintype (Γ j)] : Machine where
  Γ := Alphabet K Γ
  Q := LoaderState
  blank := default
  input := .raw
  input_injective := raw_injective
  input_ne_blank := raw_ne_blank
  start := .scan false
  transition q a := .ordinary (loaderAction k encode q a)

theorem loader_view [Fintype K] [∀ j, Fintype (Γ j)]
    (q : LoaderState) (t : Tape (Alphabet K Γ)) :
    (loaderMachine k encode).view (.run q, t) =
      .ordinary (loaderStep k encode (.run q, t)) := rfl

/-- The mirrored, tagged tape associated with a simulator stack store. -/
def represented (L : ListBlank (∀ j, Option (Γ j))) : Tape (Alphabet K Γ) :=
  TapeMirrorCompiler.mirror ((Tape.mk' ∅ (TM2to1.addBottom L)).map embedding)

inductive CheckerState where
  | first
  | second (firstMatches : Bool)
  deriving DecidableEq, Fintype

variable (aTrue : Γ k) [DecidableEq (Γ k)]

/-- The first step records the bottom-cell comparison and moves one cell left;
the second checks that the output track is empty there. Other tracks are ignored. -/
def checkerAction : CheckerState → Alphabet K Γ → Action (Alphabet K Γ) CheckerState
  | .first, a => ⟨a, .left, .run (.second (match a with
      | .raw _ => false
      | .sim b => decide (b.2 k = some aTrue)))⟩
  | .second firstMatches, a => ⟨a, .stay,
      if firstMatches && (match a with
        | .raw _ => false
        | .sim b => (b.2 k).isNone) then .accept else .reject⟩

def checkerStep : Control CheckerState × Tape (Alphabet K Γ) →
    Control CheckerState × Tape (Alphabet K Γ)
  | (.run q, t) => execute (checkerAction k aTrue q t.head) t
  | c => c

omit [DecidableEq K] in
theorem checker_two_cells (t : Tape (Alphabet K Γ)) (a b : TM2to1.Γ' K Γ)
    (ha : t.head = .sim a) (hb : t.left.head = .sim b) :
    (checkerStep k aTrue)^[2] (.run .first, t) =
      (if a.2 k = some aTrue ∧ b.2 k = none then .accept else .reject,
       t.move .left) := by
  have hw : t.write (.sim a) = t := by rw [← ha, Tape.write_self]
  have hm : (t.move .left).head = .sim b := hb
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply,
    checkerStep, ha, checkerAction, execute, hw, hm]
  have hw' : (t.move .left).write (.sim b) = t.move .left := by rw [← hm, Tape.write_self]
  rw [hw']
  cases h : b.2 k <;> simp

omit [DecidableEq K] [DecidableEq (Γ k)] in
private theorem singleton_iff_two (S : List (Γ k)) :
    (S.reverse[0]? = some aTrue ∧ S.reverse[1]? = none) ↔ S = [aTrue] := by
  constructor
  · intro h
    apply List.reverse_injective
    cases he : S.reverse with
    | nil => simp [he] at h
    | cons a as =>
      cases as with
      | nil => simpa [he] using h.1
      | cons b bs => simp [he] at h
  · rintro rfl
    simp

/-- Exactly two actual local transitions decide singleton-true source output.
The theorem applies to any valid simulator representation, including arbitrary
contents in all other tracks. -/
theorem checker_exact (L : ListBlank (∀ j, Option (Γ j))) (S : List (Γ k))
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) :
    (checkerStep k aTrue)^[2] (.run .first, represented L) =
      (if S = [aTrue] then .accept else .reject, (represented L).move .left) := by
  have hh : (represented L).head = .sim (true, L.head) := by
    simp [represented, TapeMirrorCompiler.mirror, Tape.map, Tape.mk', TM2to1.addBottom,
      embedding]
  have hl : (represented L).left.head = .sim (false, L.tail.head) := by
    simp only [represented, TapeMirrorCompiler.mirror, Tape.map, Tape.mk',
      TM2to1.addBottom, ListBlank.tail_cons, ListBlank.head_map, embedding]
  rw [checker_two_cells k aTrue _ _ _ hh hl]
  have h0 : L.head k = S.reverse[0]? := by
    simpa only [ListBlank.nth_zero] using TM2to1.stk_nth_val 0 hL
  have h1 : L.tail.head k = S.reverse[1]? := by
    simpa only [ListBlank.nth_succ, ListBlank.nth_zero] using TM2to1.stk_nth_val 1 hL
  simp only [h0, h1, singleton_iff_two k aTrue]

def checkerMachine [Fintype K] [∀ j, Fintype (Γ j)] : Machine where
  Γ := Alphabet K Γ
  Q := CheckerState
  blank := default
  input := .raw
  input_injective := raw_injective
  input_ne_blank := raw_ne_blank
  start := .first
  transition q a := .ordinary (checkerAction k aTrue q a)

theorem checker_view [Fintype K] [∀ j, Fintype (Γ j)]
    (q : CheckerState) (t : Tape (Alphabet K Γ)) :
    (checkerMachine k aTrue).view (.run q, t) =
      .ordinary (checkerStep k aTrue (.run q, t)) := rfl

end PlanarHom.TM2SingleTapeLoading
