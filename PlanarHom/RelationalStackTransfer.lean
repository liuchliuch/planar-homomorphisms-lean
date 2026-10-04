import PlanarHom.StackTransfer

/-! Transfer loops interpreted in any additive execution relation. -/

namespace PlanarHom.MachineComposition

open Turing Turing.TM2

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]
private theorem relTransferStore_cons (i j : K) (hij : i ≠ j)
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

private theorem relTransfer₂Store_cons (i j k : K)
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

variable (R : Cfg Γ Λ (σ × Option Bool) → Cfg Γ Λ (σ × Option Bool) → ℕ → Prop)
variable (trans : ∀ {c d e n t}, R c d n → R d e t → R c e (n+t))

include trans

theorem transfer_rel (i j : K) (hij : i ≠ j) (encode : Γ i → Bool) (decode : Bool → Γ j)
    (loop next : Λ)
    (one : ∀ (v : σ) (r : Option Bool) (S : ∀ k,List (Γ k)),
      R ⟨some loop,(v,r),S⟩ (stepAux (transferStmt i j encode decode loop next) (v,r) S) 1)
    (v : σ) (r : Option Bool) (S : ∀ k,List (Γ k)) :
    R ⟨some loop,(v,r),S⟩ ⟨some next,(v,none),transferStore i j (decode ∘ encode) S⟩
      ((S i).length+1) := by
  generalize hS : S i = xs
  induction xs generalizing S r with
  | nil =>
    have hu : transferStore i j (decode ∘ encode) S = S := by
      have he : Function.update S i [] = S := by rw [←hS]; exact Function.update_eq_self i S
      simp [transferStore,hS,he,Function.update_eq_self]
    simpa [hu,transferStmt_empty i j encode decode loop next v r S hS] using one v r S
  | cons a xs ih =>
    let S' := Function.update (Function.update S i xs) j (decode (encode a) :: S j)
    have hs' : S' i = xs := by simp [S',Function.update_of_ne hij]
    have h₁ := one v r S
    rw [transferStmt_cons i j hij encode decode loop next v r S a xs hS] at h₁
    have h₂ := ih none S' hs'
    rw [show transferStore i j (decode ∘ encode) S' = transferStore i j (decode ∘ encode) S
      from relTransferStore_cons i j hij (decode ∘ encode) S a xs hS] at h₂
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using trans h₁ h₂

theorem transfer₂_rel (i j k : K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (encode : Γ i → Bool) (decode₁ : Bool → Γ j) (decode₂ : Bool → Γ k)
    (loop next : Λ)
    (one : ∀ (v : σ) (r : Option Bool) (S : ∀ k,List (Γ k)),
      R ⟨some loop,(v,r),S⟩
        (stepAux (transfer₂Stmt i j k encode decode₁ decode₂ loop next) (v,r) S) 1)
    (v : σ) (r : Option Bool) (S : ∀ k,List (Γ k)) :
    R ⟨some loop,(v,r),S⟩
      ⟨some next,(v,none),transfer₂Store i j k (decode₁ ∘ encode) (decode₂ ∘ encode) S⟩
      ((S i).length+1) := by
  generalize hS : S i = xs
  induction xs generalizing S r with
  | nil =>
    have hu : transfer₂Store i j k (decode₁ ∘ encode) (decode₂ ∘ encode) S = S := by
      have he : Function.update S i [] = S := by rw [←hS]; exact Function.update_eq_self i S
      simp [transfer₂Store,transferStore,hS,he,Function.update_eq_self]
    simpa [hu,transfer₂Stmt_empty i j k encode decode₁ decode₂ loop next v r S hS]
      using one v r S
  | cons a xs ih =>
    let S' := Function.update (Function.update (Function.update S i xs)
      j (decode₁ (encode a) :: S j)) k (decode₂ (encode a) :: S k)
    have hs' : S' i = xs := by simp [S',Function.update_of_ne hij,Function.update_of_ne hik]
    have h₁ := one v r S
    rw [transfer₂Stmt_cons i j k hij hik hjk encode decode₁ decode₂ loop next v r S a xs hS] at h₁
    have h₂ := ih none S' hs'
    rw [show transfer₂Store i j k (decode₁ ∘ encode) (decode₂ ∘ encode) S' =
        transfer₂Store i j k (decode₁ ∘ encode) (decode₂ ∘ encode) S
      from relTransfer₂Store_cons i j k hij hik hjk (decode₁ ∘ encode) (decode₂ ∘ encode) S a xs hS] at h₂
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using trans h₁ h₂

theorem clear_rel (i : K) (loop next : Λ)
    (one : ∀ (v : σ) (r : Option Bool) (S : ∀ k,List (Γ k)),
      R ⟨some loop,(v,r),S⟩ (stepAux (clearStmt i loop next) (v,r) S) 1)
    (v : σ) (r : Option Bool) (S : ∀ k,List (Γ k)) :
    R ⟨some loop,(v,r),S⟩ ⟨some next,(v,none),Function.update S i []⟩ ((S i).length+1) := by
  generalize hS : S i = xs
  induction xs generalizing S r with
  | nil =>
    have hu : Function.update S i [] = S := by rw [←hS]; exact Function.update_eq_self i S
    simpa [hu,clearStmt_empty i loop next v r S hS] using one v r S
  | cons a xs ih =>
    have h₁ := one v r S
    rw [clearStmt_cons i loop next v r S a xs hS] at h₁
    have h₂ := ih none (Function.update S i xs) (by simp)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using trans h₁ h₂

end PlanarHom.MachineComposition
