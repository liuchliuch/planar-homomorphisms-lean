import PlanarHom.NaturalPowerRootMachines

/-! # Exact bounded lower-bound search in binary time

The search inspects a Boolean predicate on the interval `0,...,N`. It returns
the unique threshold when the predicate is false below that threshold and true
above it; `N+1` denotes an empty true suffix. The loop runs for the binary length
of `N+1`, even when the represented interval is exponentially large.
-/

namespace PlanarHom.IntervalBisection

abbrev State (α : Type) := α × (ℕ × ℕ)

def midpoint {α : Type} (s : State α) : ℕ := (s.2.1+s.2.2)/2

def step {α : Type} (test : α → ℕ → Bool) (s : State α) : State α :=
  if s.2.1 < s.2.2 then
    if test s.1 (midpoint s) then (s.1, s.2.1, midpoint s)
    else (s.1, midpoint s+1, s.2.2)
  else s

def initial {α : Type} (x : α) (N : ℕ) : State α := (x, 0, N+1)

def cut {α : Type} (test : α → ℕ → Bool) (x : α) (N : ℕ) : ℕ :=
  ((step test)^[Nat.size (N+1)] (initial x N)).2.1

theorem step_bound {α : Type} (test : α → ℕ → Bool) (s : State α) (B : ℕ)
    (hlo : s.2.1 ≤ B) (hhi : s.2.2 ≤ B) :
    (step test s).1 = s.1 ∧ (step test s).2.1 ≤ B ∧ (step test s).2.2 ≤ B := by
  have hm := Nat.div_add_mod (s.2.1+s.2.2) 2
  have hr := Nat.mod_lt (s.2.1+s.2.2) (by decide : 0 < 2)
  unfold step midpoint
  split_ifs <;> simp_all [midpoint] <;> omega

theorem iterate_bound {α : Type} (test : α → ℕ → Bool) (k : ℕ) (s : State α) :
    ((step test)^[k] s).1 = s.1 ∧
      ((step test)^[k] s).2.1 ≤ max s.2.1 s.2.2 ∧
      ((step test)^[k] s).2.2 ≤ max s.2.1 s.2.2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := step_bound test ((step test)^[k] s) _ ih.2.1 ih.2.2
    exact ⟨h.1.trans ih.1, h.2⟩

theorem step_brackets {α : Type} (test : α → ℕ → Bool) (x : α) (N b : ℕ)
    (ht : ∀ t < N+1, test x t = true ↔ b ≤ t) (s : State α)
    (hx : s.1 = x) (hlo : s.2.1 ≤ b) (hhi : b ≤ s.2.2) (hN : s.2.2 ≤ N+1) :
    (step test s).1 = x ∧ (step test s).2.1 ≤ b ∧
      b ≤ (step test s).2.2 ∧ (step test s).2.2 ≤ N+1 := by
  have hm := Nat.div_add_mod (s.2.1+s.2.2) 2
  have hr := Nat.mod_lt (s.2.1+s.2.2) (by decide : 0 < 2)
  unfold step
  split_ifs with ho hp
  · have hmid : midpoint s < N+1 := by unfold midpoint; omega
    have hb := (ht (midpoint s) hmid).mp (hx ▸ hp)
    exact ⟨hx, hlo, hb, by change midpoint s ≤ N+1; omega⟩
  · have hmid : midpoint s < N+1 := by unfold midpoint; omega
    have hb : ¬ b ≤ midpoint s := by
      intro hb
      exact hp (hx ▸ (ht (midpoint s) hmid).mpr hb)
    exact ⟨hx, by change midpoint s+1 ≤ b; omega, hhi, hN⟩
  · exact ⟨hx, hlo, hhi, hN⟩

theorem step_width {α : Type} (test : α → ℕ → Bool) (s : State α) (k : ℕ)
    (hw : s.2.2-s.2.1 < 2^(k+1)) :
    (step test s).2.2-(step test s).2.1 < 2^k := by
  have hpow : 2^(k+1) = 2*2^k := by rw [pow_succ]; omega
  have hpos : 0 < 2^k := pow_pos (by decide) _
  have hm := Nat.div_add_mod (s.2.1+s.2.2) 2
  have hr := Nat.mod_lt (s.2.1+s.2.2) (by decide : 0 < 2)
  unfold step midpoint
  split_ifs <;> (try dsimp only) <;> omega

theorem iterate_brackets {α : Type} (test : α → ℕ → Bool) (x : α) (N b : ℕ)
    (ht : ∀ t < N+1, test x t = true ↔ b ≤ t) (hb : b ≤ N+1) (k : ℕ) :
    ((step test)^[k] (initial x N)).1 = x ∧
      ((step test)^[k] (initial x N)).2.1 ≤ b ∧
      b ≤ ((step test)^[k] (initial x N)).2.2 ∧
      ((step test)^[k] (initial x N)).2.2 ≤ N+1 := by
  induction k with
  | zero => simpa [initial] using hb
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact step_brackets test x N b ht _ ih.1 ih.2.1 ih.2.2.1 ih.2.2.2

theorem iterate_width {α : Type} (test : α → ℕ → Bool) (x : α) (N L k : ℕ)
    (hk : k ≤ L) (hL : N+1 < 2^L) :
    ((step test)^[k] (initial x N)).2.2-
      ((step test)^[k] (initial x N)).2.1 < 2^(L-k) := by
  induction k with
  | zero => simpa [initial] using hL
  | succ k ih =>
    have hi := ih (show k ≤ L by omega)
    have he : L-k = (L-(k+1))+1 := by omega
    rw [Function.iterate_succ_apply']
    exact step_width test _ (L-(k+1)) (he ▸ hi)

/-- Exact recovery of the predicate's threshold, with an explicit right-end
sentinel. No assumption about the predicate beyond the searched interval is needed. -/
theorem cut_eq {α : Type} (test : α → ℕ → Bool) (x : α) (N b : ℕ)
    (ht : ∀ t < N+1, test x t = true ↔ b ≤ t) (hb : b ≤ N+1) :
    cut test x N = b := by
  have hs := iterate_brackets test x N b ht hb (Nat.size (N+1))
  have hw := iterate_width test x N (Nat.size (N+1)) (Nat.size (N+1))
    (by rfl) (Nat.lt_size_self (N+1))
  simp only [Nat.sub_self, pow_zero] at hw
  unfold cut
  omega

/-- Any monotone Boolean predicate has a finite threshold, with the sentinel
covering the case in which it never becomes true. -/
theorem exists_threshold (test : ℕ → Bool) (N : ℕ)
    (hm : ∀ a b, a ≤ b → b ≤ N → test a = true → test b = true) :
    ∃ b ≤ N+1, ∀ t < N+1, test t = true ↔ b ≤ t := by
  let P := fun t => (t ≤ N ∧ test t = true) ∨ t = N+1
  have hex : ∃ t, P t := ⟨N+1, Or.inr rfl⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (Or.inr rfl), ?_⟩
  intro t ht
  constructor
  · intro h
    exact Nat.find_min' hex (Or.inl ⟨by omega, h⟩)
  · intro hb
    rcases Nat.find_spec hex with h | h
    · exact hm _ t hb (by omega) h.2
    · omega

/-- Complete lower-bound specification for a monotone predicate. -/
theorem cut_spec {α : Type} (test : α → ℕ → Bool) (x : α) (N : ℕ)
    (hm : ∀ a b, a ≤ b → b ≤ N → test x a = true → test x b = true) :
    cut test x N ≤ N+1 ∧ ∀ t ≤ N, test x t = true ↔ cut test x N ≤ t := by
  obtain ⟨b, hb, ht⟩ := exists_threshold (test x) N hm
  rw [cut_eq test x N b ht hb]
  exact ⟨hb, fun t ht' => ht t (by omega)⟩

theorem cut_congr {α β : Type} (test : α → ℕ → Bool) (test' : β → ℕ → Bool)
    (x : α) (x' : β) (N : ℕ) (ht : ∀ t, test x t = test' x' t) :
    cut test x N = cut test' x' N := by
  have hi (k l h : ℕ) : ((step test)^[k] (x,l,h)).2 =
      ((step test')^[k] (x',l,h)).2 := by
    induction k generalizing l h with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [step, midpoint, ht]
      split_ifs <;> exact ih _ _
  exact congrArg Prod.fst (hi (Nat.size (N+1)) 0 (N+1))

end PlanarHom.IntervalBisection
