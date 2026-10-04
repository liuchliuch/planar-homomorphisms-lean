import PlanarHom.MachineComposition

/-!
# Genuine finite-control stack transfer loops

Each loop instruction inspects and pops one source symbol, then performs a fixed
number of pushes. The proofs count actual TM2 transitions, including the final
empty-source test. The caller's state and all unrelated stacks are retained.
-/

namespace PlanarHom.MachineComposition

open Turing Turing.TM2

variable {K Λ σ : Type} {Γ : K → Type}

/-- Move one symbol per transition, using a single optional Boolean register. -/
def transferStmt (i j : K) (encode : Γ i → Bool) (decode : Bool → Γ j)
    (loop next : Λ) : Stmt Γ Λ (σ × Option Bool) :=
  .pop i (fun v a => (v.1, a.map encode))
    (.branch (fun v => v.2.isSome)
      (.push j (fun v => decode (v.2.getD false))
        (.load (fun v => (v.1, none)) (.goto (fun _ => loop))))
      (.goto (fun _ => next)))

/-- Move one symbol to two destinations per transition. -/
def transfer₂Stmt (i j k : K) (encode : Γ i → Bool)
    (decode₁ : Bool → Γ j) (decode₂ : Bool → Γ k)
    (loop next : Λ) : Stmt Γ Λ (σ × Option Bool) :=
  .pop i (fun v a => (v.1, a.map encode))
    (.branch (fun v => v.2.isSome)
      (.push j (fun v => decode₁ (v.2.getD false))
        (.push k (fun v => decode₂ (v.2.getD false))
          (.load (fun v => (v.1, none)) (.goto (fun _ => loop)))))
      (.goto (fun _ => next)))

/-- Clear one source symbol per transition. -/
def clearStmt (i : K) (loop next : Λ) : Stmt Γ Λ (σ × Option Bool) :=
  .pop i (fun v a => (v.1, a.map (fun _ => false)))
    (.branch (fun v => v.2.isSome)
      (.load (fun v => (v.1, none)) (.goto (fun _ => loop)))
      (.goto (fun _ => next)))

variable [DecidableEq K]

/-- The complete store transformation of a one-destination transfer. -/
def transferStore (i j : K) (convert : Γ i → Γ j) (S : ∀ k, List (Γ k)) :
    ∀ k, List (Γ k) :=
  Function.update (Function.update S i []) j (((S i).map convert).reverse ++ S j)

/-- The complete store transformation of a two-destination transfer. -/
def transfer₂Store (i j k : K) (convert₁ : Γ i → Γ j) (convert₂ : Γ i → Γ k)
    (S : ∀ k, List (Γ k)) : ∀ k, List (Γ k) :=
  Function.update (transferStore i j convert₁ S) k (((S i).map convert₂).reverse ++ S k)

@[simp] theorem transferStore_source (i j : K) (hij : i ≠ j)
    (convert : Γ i → Γ j) (S : ∀ k, List (Γ k)) :
    transferStore i j convert S i = [] := by
  simp [transferStore, Function.update_of_ne hij]

@[simp] theorem transferStore_target (i j : K)
    (convert : Γ i → Γ j) (S : ∀ k, List (Γ k)) :
    transferStore i j convert S j = ((S i).map convert).reverse ++ S j := by
  simp [transferStore]

theorem transferStore_untouched (i j k : K) (hki : k ≠ i) (hkj : k ≠ j)
    (convert : Γ i → Γ j) (S : ∀ t, List (Γ t)) :
    transferStore i j convert S k = S k := by
  simp [transferStore, Function.update_of_ne hki, Function.update_of_ne hkj]

@[simp] theorem transfer₂Store_source (i j k : K) (hij : i ≠ j) (hik : i ≠ k)
    (convert₁ : Γ i → Γ j) (convert₂ : Γ i → Γ k) (S : ∀ t, List (Γ t)) :
    transfer₂Store i j k convert₁ convert₂ S i = [] := by
  simp [transfer₂Store, transferStore, Function.update_of_ne hij, Function.update_of_ne hik]

@[simp] theorem transfer₂Store_target₁ (i j k : K) (hjk : j ≠ k)
    (convert₁ : Γ i → Γ j) (convert₂ : Γ i → Γ k) (S : ∀ t, List (Γ t)) :
    transfer₂Store i j k convert₁ convert₂ S j = ((S i).map convert₁).reverse ++ S j := by
  simp [transfer₂Store, Function.update_of_ne hjk]

@[simp] theorem transfer₂Store_target₂ (i j k : K)
    (convert₁ : Γ i → Γ j) (convert₂ : Γ i → Γ k) (S : ∀ t, List (Γ t)) :
    transfer₂Store i j k convert₁ convert₂ S k = ((S i).map convert₂).reverse ++ S k := by
  simp [transfer₂Store]

theorem transfer₂Store_untouched (i j k t : K) (hti : t ≠ i) (htj : t ≠ j) (htk : t ≠ k)
    (convert₁ : Γ i → Γ j) (convert₂ : Γ i → Γ k) (S : ∀ t, List (Γ t)) :
    transfer₂Store i j k convert₁ convert₂ S t = S t := by
  simp [transfer₂Store, transferStore, Function.update_of_ne hti,
    Function.update_of_ne htj, Function.update_of_ne htk]

@[simp] theorem transferStmt_empty (i j : K) (encode : Γ i → Bool)
    (decode : Bool → Γ j) (loop next : Λ) (v : σ) (r : Option Bool)
    (S : ∀ k, List (Γ k)) (hS : S i = []) :
    stepAux (transferStmt i j encode decode loop next) (v, r) S =
      ⟨some next, (v, none), S⟩ := by
  have hu : Function.update S i [] = S := by
    rw [← hS]; exact Function.update_eq_self i S
  simp [transferStmt, hS, hu]

@[simp] theorem transferStmt_cons (i j : K) (hij : i ≠ j)
    (encode : Γ i → Bool) (decode : Bool → Γ j) (loop next : Λ)
    (v : σ) (r : Option Bool) (S : ∀ k, List (Γ k))
    (a : Γ i) (xs : List (Γ i)) (hS : S i = a :: xs) :
    stepAux (transferStmt i j encode decode loop next) (v, r) S =
      ⟨some loop, (v, none),
        Function.update (Function.update S i xs) j (decode (encode a) :: S j)⟩ := by
  simp [transferStmt, hS, Function.update_of_ne hij.symm]

@[simp] theorem transfer₂Stmt_empty (i j k : K) (encode : Γ i → Bool)
    (decode₁ : Bool → Γ j) (decode₂ : Bool → Γ k) (loop next : Λ)
    (v : σ) (r : Option Bool) (S : ∀ k, List (Γ k)) (hS : S i = []) :
    stepAux (transfer₂Stmt i j k encode decode₁ decode₂ loop next) (v, r) S =
      ⟨some next, (v, none), S⟩ := by
  have hu : Function.update S i [] = S := by
    rw [← hS]; exact Function.update_eq_self i S
  simp [transfer₂Stmt, hS, hu]

@[simp] theorem transfer₂Stmt_cons (i j k : K) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (encode : Γ i → Bool)
    (decode₁ : Bool → Γ j) (decode₂ : Bool → Γ k) (loop next : Λ)
    (v : σ) (r : Option Bool) (S : ∀ t, List (Γ t))
    (a : Γ i) (xs : List (Γ i)) (hS : S i = a :: xs) :
    stepAux (transfer₂Stmt i j k encode decode₁ decode₂ loop next) (v, r) S =
      ⟨some loop, (v, none),
        Function.update
          (Function.update (Function.update S i xs) j (decode₁ (encode a) :: S j))
          k (decode₂ (encode a) :: S k)⟩ := by
  simp [transfer₂Stmt, hS, Function.update_of_ne hij.symm,
    Function.update_of_ne hik.symm, Function.update_of_ne hjk.symm]

@[simp] theorem clearStmt_empty (i : K) (loop next : Λ) (v : σ) (r : Option Bool)
    (S : ∀ k, List (Γ k)) (hS : S i = []) :
    stepAux (clearStmt i loop next) (v, r) S = ⟨some next, (v, none), S⟩ := by
  have hu : Function.update S i [] = S := by
    rw [← hS]; exact Function.update_eq_self i S
  simp [clearStmt, hS, hu]

@[simp] theorem clearStmt_cons (i : K) (loop next : Λ) (v : σ) (r : Option Bool)
    (S : ∀ k, List (Γ k)) (a : Γ i) (xs : List (Γ i)) (hS : S i = a :: xs) :
    stepAux (clearStmt i loop next) (v, r) S =
      ⟨some loop, (v, none), Function.update S i xs⟩ := by
  simp [clearStmt, hS]

private theorem transferStore_cons (i j : K) (hij : i ≠ j)
    (convert : Γ i → Γ j) (S : ∀ k, List (Γ k))
    (a : Γ i) (xs : List (Γ i)) (hS : S i = a :: xs) :
    transferStore i j convert
      (Function.update (Function.update S i xs) j (convert a :: S j)) =
      transferStore i j convert S := by
  funext t
  by_cases htj : t = j
  · subst t
    simp [transferStore, Function.update_of_ne hij, hS, List.reverse_cons,
      List.append_assoc]
  · by_cases hti : t = i
    · subst t
      simp [transferStore, Function.update_of_ne htj]
    · simp [transferStore, Function.update_of_ne htj, Function.update_of_ne hti]

private theorem transfer₂Store_cons (i j k : K)
    (hij : i ≠ j) (hik : i ≠ k) (_hjk : j ≠ k)
    (convert₁ : Γ i → Γ j) (convert₂ : Γ i → Γ k) (S : ∀ t, List (Γ t))
    (a : Γ i) (xs : List (Γ i)) (hS : S i = a :: xs) :
    transfer₂Store i j k convert₁ convert₂
      (Function.update
        (Function.update (Function.update S i xs) j (convert₁ a :: S j))
        k (convert₂ a :: S k)) =
      transfer₂Store i j k convert₁ convert₂ S := by
  funext t
  by_cases htk : t = k
  · subst t
    simp [transfer₂Store, Function.update_of_ne hij, Function.update_of_ne hik,
      hS, List.reverse_cons, List.append_assoc]
  · by_cases htj : t = j
    · subst t
      simp [transfer₂Store, transferStore, Function.update_of_ne htk,
        Function.update_of_ne hij, Function.update_of_ne hik, hS,
        List.reverse_cons, List.append_assoc]
    · by_cases hti : t = i
      · subst t
        simp [transfer₂Store, transferStore, Function.update_of_ne htk,
          Function.update_of_ne htj]
      · simp [transfer₂Store, transferStore, Function.update_of_ne htk,
          Function.update_of_ne htj, Function.update_of_ne hti]

/-- A transfer executes exactly one actual TM2 transition per source symbol,
plus one transition to detect the empty source and enter the continuation. -/
theorem transfer_run (M : Λ → Stmt Γ Λ (σ × Option Bool))
    (i j : K) (hij : i ≠ j) (encode : Γ i → Bool) (decode : Bool → Γ j)
    (loop next : Λ) (hM : M loop = transferStmt i j encode decode loop next)
    (v : σ) (r : Option Bool) (S : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ (σ × Option Bool)) => c.bind (step M))^[(S i).length + 1]
      (some ⟨some loop, (v, r), S⟩) =
      some ⟨some next, (v, none), transferStore i j (decode ∘ encode) S⟩ := by
  generalize hS : S i = xs
  induction xs generalizing S r with
  | nil =>
      have hu : transferStore i j (decode ∘ encode) S = S := by
        have he : Function.update S i [] = S := by
          rw [← hS]; exact Function.update_eq_self i S
        simp [transferStore, hS, he, Function.update_eq_self]
      simp [hM, hS, hu]
  | cons a xs ih =>
      let S' := Function.update (Function.update S i xs) j (decode (encode a) :: S j)
      have hs' : S' i = xs := by simp [S', Function.update_of_ne hij]
      have hstep : step M ⟨some loop, (v, r), S⟩ =
          some ⟨some loop, (v, none), S'⟩ := by
        simp [hM, transferStmt_cons i j hij encode decode loop next v r S a xs hS, S']
      rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply]
      change (fun c : Option (Cfg Γ Λ (σ × Option Bool)) => c.bind (step M))^[xs.length + 1]
        (step M ⟨some loop, (v, r), S⟩) = _
      rw [hstep, ih none S' hs']
      rw [show transferStore i j (decode ∘ encode) S' =
        transferStore i j (decode ∘ encode) S from
        transferStore_cons i j hij (decode ∘ encode) S a xs hS]

/-- A two-destination copy/transfer has the same exact transition count. -/
theorem transfer₂_run (M : Λ → Stmt Γ Λ (σ × Option Bool))
    (i j k : K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (encode : Γ i → Bool) (decode₁ : Bool → Γ j) (decode₂ : Bool → Γ k)
    (loop next : Λ) (hM : M loop = transfer₂Stmt i j k encode decode₁ decode₂ loop next)
    (v : σ) (r : Option Bool) (S : ∀ t, List (Γ t)) :
    (fun c : Option (Cfg Γ Λ (σ × Option Bool)) => c.bind (step M))^[(S i).length + 1]
      (some ⟨some loop, (v, r), S⟩) =
      some ⟨some next, (v, none), transfer₂Store i j k (decode₁ ∘ encode) (decode₂ ∘ encode) S⟩ := by
  generalize hS : S i = xs
  induction xs generalizing S r with
  | nil =>
      have hu : transfer₂Store i j k (decode₁ ∘ encode) (decode₂ ∘ encode) S = S := by
        have he : Function.update S i [] = S := by
          rw [← hS]; exact Function.update_eq_self i S
        simp [transfer₂Store, transferStore, hS, he, Function.update_eq_self]
      simp [hM, hS, hu]
  | cons a xs ih =>
      let S' := Function.update
        (Function.update (Function.update S i xs) j (decode₁ (encode a) :: S j))
        k (decode₂ (encode a) :: S k)
      have hs' : S' i = xs := by
        simp [S', Function.update_of_ne hij, Function.update_of_ne hik]
      have hstep : step M ⟨some loop, (v, r), S⟩ =
          some ⟨some loop, (v, none), S'⟩ := by
        simp [hM, transfer₂Stmt_cons i j k hij hik hjk encode decode₁ decode₂ loop next
          v r S a xs hS, S']
      rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply]
      change (fun c : Option (Cfg Γ Λ (σ × Option Bool)) => c.bind (step M))^[xs.length + 1]
        (step M ⟨some loop, (v, r), S⟩) = _
      rw [hstep, ih none S' hs']
      rw [show transfer₂Store i j k (decode₁ ∘ encode) (decode₂ ∘ encode) S' =
        transfer₂Store i j k (decode₁ ∘ encode) (decode₂ ∘ encode) S from
        transfer₂Store_cons i j k hij hik hjk (decode₁ ∘ encode) (decode₂ ∘ encode) S a xs hS]

/-- Clearing preserves every other stack and the caller state. -/
theorem clear_run (M : Λ → Stmt Γ Λ (σ × Option Bool))
    (i : K) (loop next : Λ) (hM : M loop = clearStmt i loop next)
    (v : σ) (r : Option Bool) (S : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ (σ × Option Bool)) => c.bind (step M))^[(S i).length + 1]
      (some ⟨some loop, (v, r), S⟩) =
      some ⟨some next, (v, none), Function.update S i []⟩ := by
  generalize hS : S i = xs
  induction xs generalizing S r with
  | nil =>
      have he : Function.update S i [] = S := by
        rw [← hS]; exact Function.update_eq_self i S
      simp [hM, he, clearStmt_empty i loop next v r S hS]
  | cons a xs ih =>
      have hstep : step M ⟨some loop, (v, r), S⟩ =
          some ⟨some loop, (v, none), Function.update S i xs⟩ := by
        simp [hM, clearStmt_cons i loop next v r S a xs hS]
      rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply]
      change (fun c : Option (Cfg Γ Λ (σ × Option Bool)) => c.bind (step M))^[xs.length + 1]
        (step M ⟨some loop, (v, r), S⟩) = _
      rw [hstep, ih none (Function.update S i xs) (Function.update_self ..)]
      simp [Function.update_idem]

end PlanarHom.MachineComposition
