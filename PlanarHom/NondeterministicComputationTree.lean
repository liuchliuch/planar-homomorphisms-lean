import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

/-!
# Independent binary nondeterministic computation trees

A configuration is observed as a halted leaf, one ordinary successor, or two
labelled nondeterministic successors. Every active transition costs one unit.
The accepting paths are defined independently of certificates. Replay consumes
one certificate bit per transition, requires `false` at ordinary steps, and
requires an all-`false` suffix after acceptance. Thus unused time never multiplies
the number of accepting computations.
-/

namespace PlanarHom.NondeterministicComputationTree

universe u

/-- The local shape of an independent binary computation tree. -/
inductive NodeView (Cfg : Type u) where
  | reject
  | accept
  | ordinary (next : Cfg)
  | binary (nextFalse nextTrue : Cfg)

variable {Cfg : Type u}

/-- A complete accepting computation, indexed by its exact number of transitions.
The two branch constructors remain distinct even if their successors coincide. -/
inductive AcceptingPath (view : Cfg → NodeView Cfg) : Cfg → ℕ → Type u where
  | accept {c} (halt : view c = .accept) : AcceptingPath view c 0
  | ordinary {c next n} (step : view c = .ordinary next)
      (tail : AcceptingPath view next n) : AcceptingPath view c (n + 1)
  | falseBranch {c nextFalse nextTrue n} (step : view c = .binary nextFalse nextTrue)
      (tail : AcceptingPath view nextFalse n) : AcceptingPath view c (n + 1)
  | trueBranch {c nextFalse nextTrue n} (step : view c = .binary nextFalse nextTrue)
      (tail : AcceptingPath view nextTrue n) : AcceptingPath view c (n + 1)

/-- Number of accepting complete paths using at most `fuel` transitions. -/
def acceptingCount (view : Cfg → NodeView Cfg) : ℕ → Cfg → ℕ
  | 0, c => match view c with
    | .accept => 1
    | _ => 0
  | n + 1, c => match view c with
    | .reject => 0
    | .accept => 1
    | .ordinary next => acceptingCount view n next
    | .binary nextFalse nextTrue =>
        acceptingCount view n nextFalse + acceptingCount view n nextTrue

/-- Every computation has halted within the given number of transitions. -/
inductive Bounded (view : Cfg → NodeView Cfg) : Cfg → ℕ → Prop where
  | reject {c n} (halt : view c = .reject) : Bounded view c n
  | accept {c n} (halt : view c = .accept) : Bounded view c n
  | ordinary {c next n} (step : view c = .ordinary next)
      (tail : Bounded view next n) : Bounded view c (n + 1)
  | binary {c nextFalse nextTrue n} (step : view c = .binary nextFalse nextTrue)
      (left : Bounded view nextFalse n) (right : Bounded view nextTrue n) :
      Bounded view c (n + 1)

@[simp] theorem acceptingCount_accept (view : Cfg → NodeView Cfg) {c : Cfg}
    (h : view c = .accept) (n : ℕ) : acceptingCount view n c = 1 := by
  cases n <;> simp [acceptingCount, h]

@[simp] theorem acceptingCount_reject (view : Cfg → NodeView Cfg) {c : Cfg}
    (h : view c = .reject) (n : ℕ) : acceptingCount view n c = 0 := by
  cases n <;> simp [acceptingCount, h]

/-- Extra fuel does not change a computation tree whose paths have all halted. -/
theorem Bounded.acceptingCount_add {view : Cfg → NodeView Cfg} {c : Cfg} {n : ℕ}
    (h : Bounded view c n) (k : ℕ) :
    acceptingCount view (n + k) c = acceptingCount view n c := by
  induction h with
  | reject h => simp [acceptingCount_reject view h]
  | accept h => simp [acceptingCount_accept view h]
  | ordinary h tail ih => simpa [Nat.add_right_comm, acceptingCount, h] using ih
  | binary h left right ihl ihr => simp [Nat.add_right_comm, acceptingCount, h, ihl, ihr]

/-- Any larger common clock counts exactly the same complete computations. -/
theorem Bounded.acceptingCount_eq_of_le {view : Cfg → NodeView Cfg} {c : Cfg} {n m : ℕ}
    (h : Bounded view c n) (hnm : n ≤ m) :
    acceptingCount view m c = acceptingCount view n c := by
  simpa [Nat.add_sub_of_le hnm] using h.acceptingCount_add (m - n)

/-- Replay a fixed certificate. Each active step consumes exactly one bit;
ordinary steps use `false`, and halted accepting leaves permit only false padding. -/
def replay (view : Cfg → NodeView Cfg) : Cfg → List Bool → Bool
  | c, [] => match view c with
    | .accept => true
    | _ => false
  | c, b :: bs => match view c with
    | .reject => false
    | .accept => (!b) && bs.all (! ·)
    | .ordinary next => (!b) && replay view next bs
    | .binary nextFalse nextTrue => replay view (if b then nextTrue else nextFalse) bs

@[simp] theorem replay_accept (view : Cfg → NodeView Cfg) {c : Cfg}
    (h : view c = .accept) (bs : List Bool) :
    replay view c bs = bs.all (! ·) := by
  cases bs <;> simp [replay, h]

@[simp] theorem replay_reject (view : Cfg → NodeView Cfg) {c : Cfg}
    (h : view c = .reject) (bs : List Bool) : replay view c bs = false := by
  cases bs <;> simp [replay, h]

private theorem allFalse_ofFn {n : ℕ} (w : Fin n → Bool) :
    (List.ofFn w).all (! ·) = true ↔ w = fun _ => false := by
  simp only [List.all_eq_true, List.mem_ofFn]
  constructor
  · intro h
    funext i
    simpa using h (w i) ⟨i, rfl⟩
  · intro h b hb
    obtain ⟨i, rfl⟩ := hb
    simp [h]

private theorem sum_allFalse (n : ℕ) :
    (∑ w : Fin n → Bool, if (List.ofFn w).all (! ·) = true then 1 else 0) =
      (1 : ℕ) := by
  simp_rw [allFalse_ofFn]
  simp

private theorem sum_binaryWords {n : ℕ} (f : (Fin (n + 1) → Bool) → ℕ) :
    (∑ w, f w) = (∑ w : Fin n → Bool, f (Fin.cons false w)) +
      (∑ w : Fin n → Bool, f (Fin.cons true w)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f]
  rw [Fintype.sum_prod_type]
  simp [Fin.consEquiv, Nat.add_comm]

private theorem acceptingCount_eq_sum_replay (view : Cfg → NodeView Cfg)
    (n : ℕ) (c : Cfg) :
    acceptingCount view n c =
      ∑ w : Fin n → Bool, if replay view c (List.ofFn w) = true then 1 else 0 := by
  induction n generalizing c with
  | zero => cases h : view c <;> simp [acceptingCount, replay, h]
  | succ n ih =>
    cases h : view c with
    | reject => simp [acceptingCount, h]
    | accept => simpa [acceptingCount, replay_accept view h, h] using (sum_allFalse (n+1)).symm
    | ordinary next =>
      rw [sum_binaryWords]
      simp [acceptingCount, h, replay, ← ih]
    | binary nextFalse nextTrue =>
      rw [sum_binaryWords]
      simp [acceptingCount, h, replay, ← ih]

/-- Exact fixed-length certificate count. Deterministic transitions and terminal
padding contribute one encoding each; binary transitions contribute both branches. -/
theorem acceptingCount_eq_card_replay (view : Cfg → NodeView Cfg)
    (n : ℕ) (c : Cfg) :
    acceptingCount view n c =
      Fintype.card {w : Fin n → Bool // replay view c (List.ofFn w) = true} := by
  rw [acceptingCount_eq_sum_replay, Fintype.card_subtype]
  exact Finset.sum_boole _ _

namespace AcceptingPath

/-- The transition word of a complete accepting computation. -/
def word {view : Cfg → NodeView Cfg} {c : Cfg} {n : ℕ}
    (p : AcceptingPath view c n) : List Bool :=
  match p with
  | .accept _ => []
  | .ordinary _ tail => false :: tail.word
  | .falseBranch _ tail => false :: tail.word
  | .trueBranch _ tail => true :: tail.word

@[simp] theorem length_word {view : Cfg → NodeView Cfg} {c : Cfg} {n : ℕ}
    (p : AcceptingPath view c n) : p.word.length = n := by
  induction p <;> simp [word, *]

/-- Every accepting computation replays successfully with any all-false padding. -/
theorem replay_word_append {view : Cfg → NodeView Cfg} {c : Cfg} {n : ℕ}
    (p : AcceptingPath view c n) (padding : ℕ) :
    replay view c (p.word ++ List.replicate padding false) = true := by
  induction p with
  | accept h => simp [word, replay_accept view h]
  | ordinary h tail ih => simp [word, replay, h, ih]
  | falseBranch h tail ih => simp [word, replay, h, ih]
  | trueBranch h tail ih => simp [word, replay, h, ih]

/-- Equal padded transition words identify the complete computation, including
its exact transition count. This rules out both padding multiplicity and merged
branch multiplicity. -/
theorem padded_word_injective {view : Cfg → NodeView Cfg} {c : Cfg} {n m : ℕ}
    (p : AcceptingPath view c n) (q : AcceptingPath view c m) (a b : ℕ)
    (h : p.word ++ List.replicate a false = q.word ++ List.replicate b false) :
    (⟨n, p⟩ : Σ k, AcceptingPath view c k) = ⟨m, q⟩ := by
  induction p generalizing m with
  | accept hp =>
    cases q with
    | accept hq => rfl
    | ordinary hq tail => cases hp.symm.trans hq
    | falseBranch hq tail => cases hp.symm.trans hq
    | trueBranch hq tail => cases hp.symm.trans hq
  | @ordinary c next n hp tail ih =>
    cases q with
    | accept hq => cases hp.symm.trans hq
    | @ordinary _ next' m hq tail' =>
      have hn : next = next' := NodeView.ordinary.inj (hp.symm.trans hq)
      subst next'
      have he := ih tail' (List.cons.inj h).2
      cases he
      rfl
    | falseBranch hq tail' => cases hp.symm.trans hq
    | trueBranch hq tail' => cases hp.symm.trans hq
  | @falseBranch c nextFalse nextTrue n hp tail ih =>
    cases q with
    | accept hq => cases hp.symm.trans hq
    | ordinary hq tail' => cases hp.symm.trans hq
    | @falseBranch _ nextFalse' nextTrue' m hq tail' =>
      obtain ⟨hl, hr⟩ := NodeView.binary.inj (hp.symm.trans hq)
      subst nextFalse'
      subst nextTrue'
      have he := ih tail' (List.cons.inj h).2
      cases he
      rfl
    | trueBranch hq tail' => simp [word] at h
  | @trueBranch c nextFalse nextTrue n hp tail ih =>
    cases q with
    | accept hq => cases hp.symm.trans hq
    | ordinary hq tail' => cases hp.symm.trans hq
    | falseBranch hq tail' => simp [word] at h
    | @trueBranch _ nextFalse' nextTrue' m hq tail' =>
      obtain ⟨hl, hr⟩ := NodeView.binary.inj (hp.symm.trans hq)
      subst nextFalse'
      subst nextTrue'
      have he := ih tail' (List.cons.inj h).2
      cases he
      rfl

end AcceptingPath

private theorem allFalse_eq_replicate (bs : List Bool) :
    bs.all (! ·) = true → bs = List.replicate bs.length false := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    cases b with
    | false =>
      intro h
      have hh := ih (by simpa using h)
      exact congrArg (List.cons false) hh
    | true => simp

/-- Every successful replay determines a complete accepting path and its unique
all-false suffix. The path semantics do not mention replay or certificates. -/
theorem replay_sound (view : Cfg → NodeView Cfg) (c : Cfg) (bs : List Bool)
    (h : replay view c bs = true) :
    ∃ n, ∃ p : AcceptingPath view c n,
      n ≤ bs.length ∧ bs = p.word ++ List.replicate (bs.length - n) false := by
  induction bs generalizing c with
  | nil =>
    cases hv : view c <;> simp [replay, hv] at h
    exact ⟨0, .accept hv, by simp, by simp [AcceptingPath.word]⟩
  | cons b bs ih =>
    cases hv : view c with
    | reject => simp [replay, hv] at h
    | accept =>
      refine ⟨0, .accept hv, by omega, ?_⟩
      simpa [AcceptingPath.word] using
        allFalse_eq_replicate (b :: bs) (by simpa [replay, hv] using h)
    | ordinary next =>
      cases b with
      | true => simp [replay, hv] at h
      | false =>
        obtain ⟨n, p, hn, hp⟩ := ih next (by simpa [replay, hv] using h)
        refine ⟨n+1, .ordinary hv p, by simpa using hn, ?_⟩
        simpa [AcceptingPath.word] using congrArg (List.cons false) hp
    | binary nextFalse nextTrue =>
      cases b with
      | false =>
        obtain ⟨n, p, hn, hp⟩ := ih nextFalse (by simpa [replay, hv] using h)
        refine ⟨n+1, .falseBranch hv p, by simpa using hn, ?_⟩
        simpa [AcceptingPath.word] using congrArg (List.cons false) hp
      | true =>
        obtain ⟨n, p, hn, hp⟩ := ih nextTrue (by simpa [replay, hv] using h)
        refine ⟨n+1, .trueBranch hv p, by simpa using hn, ?_⟩
        simpa [AcceptingPath.word] using congrArg (List.cons true) hp

/-- The actual complete accepting computations whose transition counts meet the
clock. This type is defined directly from paths, without mentioning certificates. -/
abbrev BoundedAcceptingPath (view : Cfg → NodeView Cfg) (c : Cfg) (fuel : ℕ) :=
  {p : Σ n, AcceptingPath view c n // p.1 ≤ fuel}

private def fixedWord (bs : List Bool) {n : ℕ} (h : bs.length = n) : Fin n → Bool :=
  fun i => bs.get (Fin.cast h.symm i)

private theorem ofFn_fixedWord (bs : List Bool) {n : ℕ} (h : bs.length = n) :
    List.ofFn (fixedWord bs h) = bs := by
  subst n
  exact List.ofFn_get bs

namespace BoundedAcceptingPath

/-- Encode a complete computation by its transition bits, followed by the unique
false padding needed to fill the clock. -/
def certificate {view : Cfg → NodeView Cfg} {c : Cfg} {fuel : ℕ}
    (p : BoundedAcceptingPath view c fuel) :
    {w : Fin fuel → Bool // replay view c (List.ofFn w) = true} := by
  let bs := p.val.snd.word ++ List.replicate (fuel - p.val.fst) false
  have hlen : bs.length = fuel := by
    simp [bs, Nat.add_sub_of_le p.property]
  refine ⟨fixedWord bs hlen, ?_⟩
  rw [ofFn_fixedWord]
  exact p.val.snd.replay_word_append (fuel - p.val.fst)

@[simp] theorem ofFn_certificate {view : Cfg → NodeView Cfg} {c : Cfg} {fuel : ℕ}
    (p : BoundedAcceptingPath view c fuel) :
    List.ofFn p.certificate.val = p.val.snd.word ++ List.replicate (fuel - p.val.fst) false := by
  simp only [certificate, ofFn_fixedWord]

/-- The padding convention gives precisely one certificate per computation. -/
theorem certificate_injective {view : Cfg → NodeView Cfg} {c : Cfg} {fuel : ℕ} :
    Function.Injective (certificate (view := view) (c := c) (fuel := fuel)) := by
  intro p q h
  apply Subtype.ext
  apply AcceptingPath.padded_word_injective p.val.snd q.val.snd
  have he := congrArg (fun w => List.ofFn w.val) h
  simpa using he

/-- Every accepted fixed-length word comes from an actual complete computation. -/
theorem certificate_surjective {view : Cfg → NodeView Cfg} {c : Cfg} {fuel : ℕ} :
    Function.Surjective (certificate (view := view) (c := c) (fuel := fuel)) := by
  intro w
  obtain ⟨n, p, hn, hp⟩ := replay_sound view c (List.ofFn w.val) w.property
  have hn' : n ≤ fuel := by simpa using hn
  refine ⟨⟨⟨n, p⟩, hn'⟩, ?_⟩
  apply Subtype.ext
  apply List.ofFn_inj.mp
  simpa using hp.symm

end BoundedAcceptingPath

/-- Explicit one-to-one correspondence between independent complete paths and
accepted padded fixed-length certificates. -/
noncomputable def acceptingPathEquivCertificates (view : Cfg → NodeView Cfg)
    (c : Cfg) (fuel : ℕ) :
    BoundedAcceptingPath view c fuel ≃
      {w : Fin fuel → Bool // replay view c (List.ofFn w) = true} :=
  Equiv.ofBijective BoundedAcceptingPath.certificate
    ⟨BoundedAcceptingPath.certificate_injective, BoundedAcceptingPath.certificate_surjective⟩

noncomputable instance boundedAcceptingPathFintype (view : Cfg → NodeView Cfg)
    (c : Cfg) (fuel : ℕ) : Fintype (BoundedAcceptingPath view c fuel) :=
  Fintype.ofEquiv _ (acceptingPathEquivCertificates view c fuel).symm

/-- The recursive accepting count is the cardinality of the independent path
semantics, in addition to being the cardinality of accepted certificates. -/
theorem acceptingCount_eq_card_paths (view : Cfg → NodeView Cfg) (n : ℕ) (c : Cfg) :
    acceptingCount view n c = Fintype.card (BoundedAcceptingPath view c n) := by
  rw [acceptingCount_eq_card_replay]
  exact Fintype.card_congr (acceptingPathEquivCertificates view c n).symm

/-- A bound on all branches bounds the length of every complete accepting path. -/
theorem Bounded.path_length_le {view : Cfg → NodeView Cfg} {c : Cfg} {fuel n : ℕ}
    (h : Bounded view c fuel) (p : AcceptingPath view c n) : n ≤ fuel := by
  induction h generalizing n with
  | reject hv =>
    cases p with
    | accept hp => cases hv.symm.trans hp
    | ordinary hp tail => cases hv.symm.trans hp
    | falseBranch hp tail => cases hv.symm.trans hp
    | trueBranch hp tail => cases hv.symm.trans hp
  | accept hv =>
    cases p with
    | accept hp => exact Nat.zero_le _
    | ordinary hp tail => cases hv.symm.trans hp
    | falseBranch hp tail => cases hv.symm.trans hp
    | trueBranch hp tail => cases hv.symm.trans hp
  | @ordinary c next fuel hv tail ih =>
    cases p with
    | accept hp => cases hv.symm.trans hp
    | @ordinary _ next' n hp tail' =>
      have hn : next = next' := NodeView.ordinary.inj (hv.symm.trans hp)
      subst next'
      exact Nat.succ_le_succ (ih tail')
    | falseBranch hp tail' => cases hv.symm.trans hp
    | trueBranch hp tail' => cases hv.symm.trans hp
  | @binary c nextFalse nextTrue fuel hv left right ihl ihr =>
    cases p with
    | accept hp => cases hv.symm.trans hp
    | ordinary hp tail => cases hv.symm.trans hp
    | @falseBranch _ nextFalse' nextTrue' n hp tail =>
      obtain ⟨hl, hr⟩ := NodeView.binary.inj (hv.symm.trans hp)
      subst nextFalse'
      subst nextTrue'
      exact Nat.succ_le_succ (ihl tail)
    | @trueBranch _ nextFalse' nextTrue' n hp tail =>
      obtain ⟨hl, hr⟩ := NodeView.binary.inj (hv.symm.trans hp)
      subst nextFalse'
      subst nextTrue'
      exact Nat.succ_le_succ (ihr tail)

/-- Under an all-branch time bound, bounding complete accepting computations
removes no path at all. -/
def Bounded.completePathEquiv {view : Cfg → NodeView Cfg} {c : Cfg} {fuel : ℕ}
    (h : Bounded view c fuel) :
    (Σ n, AcceptingPath view c n) ≃ BoundedAcceptingPath view c fuel where
  toFun p := ⟨p, h.path_length_le p.snd⟩
  invFun p := p.val
  left_inv _ := rfl
  right_inv _ := rfl

/-- All complete accepting paths form a finite type whenever all branches halt
within a common clock. -/
noncomputable def Bounded.completePathsFintype {view : Cfg → NodeView Cfg}
    {c : Cfg} {fuel : ℕ} (h : Bounded view c fuel) :
    Fintype (Σ n, AcceptingPath view c n) :=
  Fintype.ofEquiv _ h.completePathEquiv.symm

/-- The clocked count equals the number of all complete accepting paths of a
bounded tree, with no certificate or bounded-path predicate in the counted type. -/
theorem Bounded.acceptingCount_eq_card_completePaths {view : Cfg → NodeView Cfg}
    {c : Cfg} {fuel : ℕ} (h : Bounded view c fuel) :
    letI := h.completePathsFintype
    acceptingCount view fuel c = Fintype.card (Σ n, AcceptingPath view c n) := by
  letI := h.completePathsFintype
  exact (acceptingCount_eq_card_paths view fuel c).trans
    (Fintype.card_congr h.completePathEquiv.symm)

end PlanarHom.NondeterministicComputationTree
