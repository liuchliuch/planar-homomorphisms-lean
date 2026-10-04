import PlanarHom.TM2TapeStatementBounds
import PlanarHom.NondeterministicBlockSimulation

/-! # Tape simulation traces that stop at source instruction boundaries

Only scanning and return labels execute in `scanView`. A normal source label is
an endpoint, allowing a later compiler to install a genuine binary choice there.
Thus these traces cannot accidentally execute a source choice deterministically.
-/
namespace PlanarHom.TM2TapeBoundaryRuns
open Turing Turing.TM2to1 MachineComposition TM2TapeStatementBounds
open NondeterministicComputationTree NondeterministicBlockSimulation

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]
abbrev Cfg := TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ

/-- Deterministic internal scan nodes; all source boundaries are stopped. -/
def scanView (M : Λ → TM2.Stmt Γ Λ σ) (c : Cfg (Γ:=Γ) (Λ:=Λ) (σ:=σ)) :
    NodeView (Cfg (Γ:=Γ) (Λ:=Λ) (σ:=σ)) :=
  match c.l with
  | some (.go k a q) => .ordinary (TM1.stepAux (tr M (.go k a q)) c.var c.Tape)
  | some (.ret q) => .ordinary (TM1.stepAux (tr M (.ret q)) c.var c.Tape)
  | _ => .reject

/-- Outbound scans contain only internal `go` states. -/
theorem outbound (M : Λ → TM2.Stmt Γ Λ σ) {k : K}
    (action : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : List (Γ k)) (L : ListBlank (∀ k, Option (Γ k)))
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n ≤ S.length) :
    OrdinaryRun (scanView M) n ⟨some (.go k action q),v,Tape.mk' ∅ (addBottom L)⟩
      ⟨some (.go k action q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    have hs : scanView M ⟨some (.go k action q),v,
        (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ =
        .ordinary ⟨some (.go k action q),v,
          (Tape.move Dir.right)^[n+1] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [scanView,TM1.stepAux,tr,Tape.mk'_nth_nat,Tape.move_right_n_head,addBottom_nth_snd]
      rw [stk_nth_val _ hL,List.getElem?_eq_getElem (by simpa only [List.length_reverse] using hn)]
      simp only [Option.isNone_some,Bool.cond_false,Function.iterate_succ_apply']
    exact (ih (Nat.le_of_succ_le hn)).trans (.cons hs (.nil _))

/-- Return scans contain only internal `ret` states. -/
theorem inbound (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    OrdinaryRun (scanView M) n
      ⟨some (.ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (.ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    apply OrdinaryRun.cons (next := ⟨some (.ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩) _ ih
    simp only [scanView]
    rw [tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_succ_fst]
    simp only [Bool.cond_false,TM1.stepAux,Function.iterate_succ_apply',Tape.move_right_left]

/-- A complete stack operation stops before running its return continuation. -/
theorem stackAction (M : Λ → TM2.Stmt Γ Λ σ) {k : K}
    (action : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k,List (Γ k)) (L : ListBlank (∀ k,Option (Γ k)))
    (hL : ∀ k,L.map (proj k)=ListBlank.mk ((S k).map some).reverse) :
    ∃ L' : ListBlank (∀ k,Option (Γ k)),
      (∀ j,L'.map (proj j)=ListBlank.mk (((Function.update S k (stWrite v (S k) action)) j).map some).reverse) ∧
      OrdinaryRun (scanView M) ((S k).length+1+(stWrite v (S k) action).length)
        ⟨some (.go k action q),v,Tape.mk' ∅ (addBottom L)⟩
        ⟨some (.ret q),stVar v (S k) action,Tape.mk' ∅ (addBottom L')⟩ := by
  obtain ⟨L',hL',hop⟩ := tr_respects_aux₂
    (q:=TM1.Stmt.goto (fun _ _ => Λ'.ret q)) (v:=v) hL action
  have hs : scanView M
      ⟨some (.go k action q),v,(Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩ =
      .ordinary ⟨some (.ret q),stVar v (S k) action,
        (Tape.move Dir.right)^[(stWrite v (S k) action).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
    simp only [scanView,tr,TM1.stepAux]
    rw [Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,stk_nth_val _ (hL k)]
    rw [List.getElem?_eq_none (by simp)]
    simp only [Option.isNone_none,Bool.cond_true]
    simpa only [TM1.stepAux,Function.update_self] using congrArg NodeView.ordinary hop
  refine ⟨L',hL',?_⟩
  exact ((outbound M action q v (S k) L (hL k) (S k).length le_rfl).trans
    (.cons hs (.nil _))).trans (inbound M q (stVar v (S k) action) L' _)

/-- Execute the return continuation in one macro transition. -/
theorem return_step (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (L : ListBlank (∀k,Option (Γ k))) :
    scanView M ⟨some (.ret q),v,Tape.mk' ∅ (addBottom L)⟩ =
      .ordinary (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) := by
  simp only [scanView,tr,TM1.stepAux,Tape.mk'_head,addBottom_head_fst,Bool.cond_true]

/-- The exact source result is reached without executing another normal label.
The bound charges actual TM1 macro transitions, to be refined into primitives. -/
theorem residual (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀k,List (Γ k)) (L : ListBlank (∀k,Option (Γ k)))
    (hL : ∀k,L.map (proj k)=ListBlank.mk ((S k).map some).reverse)
    (n : ℕ) (hS : ∀k,(S k).length≤n) :
    ∃ t c, TrCfg (TM2.stepAux q v S) c ∧
      t ≤ stackOps q*(2*(n+pushBound q)+3) ∧
      OrdinaryRun (scanView M) t
        (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) c := by
  induction q using stmtStRec generalizing v S L n with
  | run k a q ih =>
    obtain ⟨L',hL',ha⟩ := stackAction M a q v S L hL
    obtain ⟨t,c,hc,ht,hr⟩ := ih (stVar v (S k) a)
      (Function.update S k (stWrite v (S k) a)) L' hL' (n+adds a)
      (action_length_bound a v S n hS)
    refine ⟨((S k).length+1+(stWrite v (S k) a).length)+1+t,c,?_,?_,?_⟩
    · simpa only [step_run] using hc
    · rw [stackOps_stRun,pushBound_stRun]
      have hp := TM2TapeScanBounds.stackAction_cost_le a v (S k)
      have hs := hS k
      have hcost : (S k).length+1+(stWrite v (S k) a).length+1 ≤
          2*(n+pushBound q+adds a)+3 := by omega
      have he : n+adds a+pushBound q=n+pushBound q+adds a := by omega
      rw [he] at ht
      calc
        _ ≤ (2*(n+pushBound q+adds a)+3)+stackOps q*(2*(n+pushBound q+adds a)+3) :=
          Nat.add_le_add hcost ht
        _ = (stackOps q+1)*(2*(n+(pushBound q+adds a))+3) := by ring
    · rw [trNormal_run]
      exact (ha.trans (.cons (return_step M q _ L') (.nil _))).trans hr
  | load f q ih =>
    simpa only [stackOps,pushBound,trNormal,TM1.stepAux,TM2.stepAux] using ih (f v) S L hL n hS
  | branch f q r ihq ihr =>
    cases hf : f v with
    | false =>
      obtain ⟨t,c,hc,ht,hr⟩ := ihr v S L hL n hS
      refine ⟨t,c,?_,?_,?_⟩
      · simpa only [TM2.stepAux,hf,Bool.cond_false] using hc
      · apply ht.trans
        exact Nat.mul_le_mul (Nat.le_add_left _ _) (by simp only [pushBound]; omega)
      · simpa only [trNormal,TM1.stepAux,hf,Bool.cond_false] using hr
    | true =>
      obtain ⟨t,c,hc,ht,hr⟩ := ihq v S L hL n hS
      refine ⟨t,c,?_,?_,?_⟩
      · simpa only [TM2.stepAux,hf,Bool.cond_true] using hc
      · apply ht.trans
        exact Nat.mul_le_mul (Nat.le_add_right _ _) (by simp only [pushBound]; omega)
      · simpa only [trNormal,TM1.stepAux,hf,Bool.cond_true] using hr
  | goto f => exact ⟨0,_,⟨L,hL⟩,Nat.zero_le _,.nil _⟩
  | halt => exact ⟨0,_,⟨L,hL⟩,Nat.zero_le _,.nil _⟩

end PlanarHom.TM2TapeBoundaryRuns
