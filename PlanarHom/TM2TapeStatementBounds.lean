import PlanarHom.TM2TapeScanBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Costed simulation of one full TM2 statement on mathlib's tape machine -/
namespace PlanarHom.TM2TapeStatementBounds
open Turing Turing.TM2to1 MachineComposition TM2TapeScanBounds

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def stackOps : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => stackOps q+1
  | .peek _ _ q => stackOps q+1
  | .pop _ _ q => stackOps q+1
  | .load _ q => stackOps q
  | .branch _ q r => stackOps q+stackOps r
  | .goto _ => 0
  | .halt => 0

def adds {k : K} : StAct K Γ σ k → ℕ
  | .push _ => 1
  | .peek _ => 0
  | .pop _ => 0

omit [DecidableEq K] in
theorem stackOps_stRun {k : K} (a : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    stackOps (stRun a q) = stackOps q+1 := by cases a <;> rfl

omit [DecidableEq K] in
theorem pushBound_stRun {k : K} (a : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    pushBound (stRun a q) = pushBound q+adds a := by cases a <;> simp [stRun,pushBound,adds]

theorem action_length_bound {k : K} (a : StAct K Γ σ k) (v : σ)
    (S : ∀k,List (Γ k)) (n : ℕ) (hS : ∀k,(S k).length≤n) :
    ∀j,((Function.update S k (stWrite v (S k) a)) j).length≤n+adds a := by
  intro j
  by_cases h : j=k
  · subst j
    have hs := hS k
    cases a <;> simp only [Function.update_self,stWrite,adds,List.length_cons,List.length_tail] <;> omega
  · simp only [Function.update_of_ne h]
    exact (hS j).trans (Nat.le_add_right _ _)

/-- The continuation at the bottom executes the remaining fixed statement in
one TM1 transition, without traversing any tape segment. -/
theorem return_step (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (L : ListBlank (∀k,Option (Γ k))) :
    TM1.step (tr M) ⟨some (.ret q),v,Tape.mk' ∅ (addBottom L)⟩ =
      some (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) := by
  simp only [TM1.step,tr,TM1.stepAux,Tape.mk'_head,addBottom_head_fst,Bool.cond_true]

/-- The residual simulation following entry into a fixed source statement has
a proved linear bound in its materialized stack size. -/
theorem residual (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀k,List (Γ k)) (L : ListBlank (∀k,Option (Γ k)))
    (hL : ∀k,L.map (proj k)=ListBlank.mk ((S k).map some).reverse)
    (n : ℕ) (hS : ∀k,(S k).length≤n) :
    ∃ t c, TrCfg (TM2.stepAux q v S) c ∧
      t ≤ stackOps q*(2*(n+pushBound q)+3) ∧
      iter M t (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) = some c := by
  induction q using stmtStRec generalizing v S L n with
  | run k a q ih =>
    obtain ⟨L',hL',ha⟩ := stackAction M a q v S L hL
    obtain ⟨t,c,hc,ht,hr⟩ := ih (stVar v (S k) a)
      (Function.update S k (stWrite v (S k) a)) L' hL' (n+adds a)
      (action_length_bound a v S n hS)
    refine ⟨((S k).length+1+(stWrite v (S k) a).length)+1+t,c,?_,?_,?_⟩
    · simpa only [step_run] using hc
    · rw [stackOps_stRun,pushBound_stRun]
      have hp := stackAction_cost_le a v (S k)
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
      change iter M _ ⟨some (.go k a q),v,Tape.mk' ∅ (addBottom L)⟩ = _
      exact iter_trans M (iter_trans M ha (show iter M 1 _ = _ from return_step M q _ L')) hr
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
  | goto f => exact ⟨0,_,⟨L,hL⟩,Nat.zero_le _,rfl⟩
  | halt => exact ⟨0,_,⟨L,hL⟩,Nat.zero_le _,rfl⟩

/-- One genuine source transition admits a real bounded tape execution.
The leading dispatch transition is explicitly included. -/
theorem source_step (M : Λ → TM2.Stmt Γ Λ σ) (l : Λ) (v : σ)
    (S : ∀k,List (Γ k)) (L : ListBlank (∀k,Option (Γ k)))
    (hL : ∀k,L.map (proj k)=ListBlank.mk ((S k).map some).reverse)
    (n : ℕ) (hS : ∀k,(S k).length≤n) :
    ∃ t c, TrCfg (TM2.stepAux (M l) v S) c ∧
      t ≤ 1+stackOps (M l)*(2*(n+pushBound (M l))+3) ∧
      iter M t ⟨some (.normal l),v,Tape.mk' ∅ (addBottom L)⟩ = some c := by
  obtain ⟨t,c,hc,ht,hr⟩ := residual M (M l) v S L hL n hS
  exact ⟨1+t,c,hc,Nat.add_le_add_left ht 1,iter_trans M (show iter M 1 _ = _ from rfl) hr⟩

end PlanarHom.TM2TapeStatementBounds
