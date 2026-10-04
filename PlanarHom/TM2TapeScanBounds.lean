import PlanarHom.MachineComposition

/-! # Exact transition counts for mathlib's multistack tape scans

These are costed refinements of mathlib's unbounded `TM2to1` scan lemmas.
They do not by themselves assert a complete polynomial-time single-tape compiler.
-/
namespace PlanarHom.TM2TapeScanBounds
open Turing Turing.TM2to1

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

abbrev TargetCfg := TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ

def iter (M : Λ → TM2.Stmt Γ Λ σ) (n : ℕ) (c : TargetCfg (Γ:=Γ) (Λ:=Λ) (σ:=σ)) :
    Option (TargetCfg (Γ:=Γ) (Λ:=Λ) (σ:=σ)) :=
  (fun c : Option (TargetCfg (Γ:=Γ) (Λ:=Λ) (σ:=σ)) => c.bind (TM1.step (tr M)))^[n] (some c)

/-- Scanning from the common stack bottom to depth `n` takes exactly `n`
TM1 transitions while that depth is within the selected stack. -/
theorem outbound (M : Λ → TM2.Stmt Γ Λ σ) {k : K}
    (action : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : List (Γ k)) (L : ListBlank (∀ k, Option (Γ k)))
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n ≤ S.length) :
    iter M n ⟨some (.go k action q),v,Tape.mk' ∅ (addBottom L)⟩ =
      some ⟨some (.go k action q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold iter at *
    rw [Function.iterate_succ_apply',ih (Nat.le_of_succ_le hn)]
    change TM1.step (tr M) ⟨some (.go k action q),v,
      (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ = _
    simp only [TM1.step,TM1.stepAux,tr,Tape.mk'_nth_nat,Tape.move_right_n_head,
      addBottom_nth_snd]
    rw [stk_nth_val _ hL,List.getElem?_eq_getElem (by simpa only [List.length_reverse] using hn)]
    simp only [Option.isNone_some,Bool.cond_false,Function.iterate_succ_apply']

/-- Returning from depth `n` to the marked bottom takes exactly `n` TM1
transitions; the continuation is not executed during these transitions. -/
theorem inbound (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    iter M n ⟨some (.ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ =
      some ⟨some (.ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iter,Function.iterate_succ_apply]
    have hs : TM1.step (tr M)
        ⟨some (.ret q),v,(Tape.move Dir.right)^[n+1] (Tape.mk' ∅ (addBottom L))⟩ =
        some ⟨some (.ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [TM1.step]
      rw [tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_succ_fst]
      simp only [Bool.cond_false,TM1.stepAux,Function.iterate_succ_apply',Tape.move_right_left]
    simp only [Option.bind_some]
    rw [hs]
    exact ih


theorem iter_trans (M : Λ → TM2.Stmt Γ Λ σ) {c d e : TargetCfg (Γ:=Γ) (Λ:=Λ) (σ:=σ)}
    {n k : ℕ} (h : iter M n c = some d) (h' : iter M k d = some e) :
    iter M (n+k) c = some e := by
  rw [Nat.add_comm,iter,Function.iterate_add_apply]
  change (fun c : Option (TargetCfg (Γ:=Γ) (Λ:=Λ) (σ:=σ)) => c.bind (TM1.step (tr M)))^[k]
    (iter M n c) = _
  rw [h]
  exact h'

/-- A complete stack operation scans to its top, performs the fixed local
operation, and returns to the bottom. Its exact transition count is the old
stack length plus the new stack length plus one. -/
theorem stackAction (M : Λ → TM2.Stmt Γ Λ σ) {k : K}
    (action : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k,List (Γ k)) (L : ListBlank (∀ k,Option (Γ k)))
    (hL : ∀ k,L.map (proj k)=ListBlank.mk ((S k).map some).reverse) :
    ∃ L' : ListBlank (∀ k,Option (Γ k)),
      (∀ j,L'.map (proj j)=ListBlank.mk (((Function.update S k (stWrite v (S k) action)) j).map some).reverse) ∧
      iter M ((S k).length+1+(stWrite v (S k) action).length)
        ⟨some (.go k action q),v,Tape.mk' ∅ (addBottom L)⟩ =
        some ⟨some (.ret q),stVar v (S k) action,Tape.mk' ∅ (addBottom L')⟩ := by
  obtain ⟨L',hL',hop⟩ := tr_respects_aux₂
    (q:=TM1.Stmt.goto (fun _ _ => Λ'.ret q)) (v:=v) hL action
  have hs : TM1.step (tr M)
      ⟨some (.go k action q),v,(Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩ =
      some ⟨some (.ret q),stVar v (S k) action,
        (Tape.move Dir.right)^[(stWrite v (S k) action).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
    simp only [TM1.step,tr,TM1.stepAux]
    rw [Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,stk_nth_val _ (hL k)]
    rw [List.getElem?_eq_none (by simp)]
    simp only [Option.isNone_none,Bool.cond_true]
    simpa only [TM1.stepAux,Function.update_self] using congrArg some hop
  have ho := outbound M action q v (S k) L (hL k) (S k).length (Nat.le_refl _)
  have hi := inbound M q (stVar v (S k) action) L' (stWrite v (S k) action).length
  refine ⟨L',hL',iter_trans M (iter_trans M ho ?_) hi⟩
  exact hs

omit [DecidableEq K] in
/-- Push changes length by one; pop/peek never increase it. The finite local
stack operation therefore costs at most twice the old length plus two. -/
theorem stackAction_cost_le {k : K} (action : StAct K Γ σ k) (v : σ) (S : List (Γ k)) :
    S.length+1+(stWrite v S action).length ≤ 2*S.length+2 := by
  cases action <;> simp only [stWrite,List.length_cons,List.length_tail] <;> omega

end PlanarHom.TM2TapeScanBounds
