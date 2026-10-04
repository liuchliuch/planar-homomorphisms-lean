import PlanarHom.CountingCookLevinNorMachines

/-! Constructive NOR formulas for every fixed finite Boolean truth table.
These templates are fixed machine data. They will be reused at every tape cell
and clock layer, rather than tabulating the exponentially many global states. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
namespace Expr

def neg {V : Type} (e : Expr V) : Expr V := .nor e e

def conj {V : Type} (a b : Expr V) : Expr V := .nor a.neg b.neg

def disj {V : Type} (a b : Expr V) : Expr V := (Expr.nor a b).neg

@[simp] theorem eval_neg {V : Type} (ρ : V → Bool) (e : Expr V) : e.neg.eval ρ= !(e.eval ρ) := by
  simp [neg,eval]
@[simp] theorem eval_conj {V : Type} (ρ : V → Bool) (a b : Expr V) :
    (conj a b).eval ρ=(a.eval ρ && b.eval ρ) := by simp [conj,eval,Bool.not_or]
@[simp] theorem eval_disj {V : Type} (ρ : V → Bool) (a b : Expr V) :
    (disj a b).eval ρ=(a.eval ρ || b.eval ρ) := by simp [disj,eval]

def rename {V W : Type} (r : V → W) : Expr V → Expr W
  | .var v => .var (r v)
  | .nor a b => .nor (a.rename r) (b.rename r)

@[simp] theorem eval_rename {V W : Type} (r : V → W) (ρ : W → Bool) (e : Expr V) :
    (e.rename r).eval ρ=e.eval (ρ ∘ r) := by
  induction e with
  | var v => rfl
  | nor a b ha hb => simp only [rename,eval,ha,hb]

@[simp] theorem gates_rename {V W : Type} (r : V → W) (e : Expr V) :
    (e.rename r).gates=e.gates := by
  induction e with
  | var v => rfl
  | nor a b ha hb => simp only [rename,gates,ha,hb]

/-- Two distinguished ground wires carry fixed false and true values. -/
def grounded {V : Type} (ρ : V → Bool) : V ⊕ Bool → Bool := Sum.elim ρ id

def allExpr {V : Type} (es : List (Expr (V ⊕ Bool))) : Expr (V ⊕ Bool) :=
  es.foldr conj (.var (.inr true))

def anyExpr {V : Type} (es : List (Expr (V ⊕ Bool))) : Expr (V ⊕ Bool) :=
  es.foldr disj (.var (.inr false))

@[simp] theorem eval_allExpr {V : Type} (ρ : V → Bool) (es : List (Expr (V ⊕ Bool))) :
    (allExpr es).eval (grounded ρ)=es.all (fun e => e.eval (grounded ρ)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [allExpr,List.foldr_cons,eval_conj,List.all_cons,← ih]

@[simp] theorem eval_anyExpr {V : Type} (ρ : V → Bool) (es : List (Expr (V ⊕ Bool))) :
    (anyExpr es).eval (grounded ρ)=es.any (fun e => e.eval (grounded ρ)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [anyExpr,List.foldr_cons,eval_disj,List.any_cons,← ih]

def literal {d : ℕ} (σ : Fin d → Bool) (i : Fin d) : Expr (Fin d ⊕ Bool) :=
  if σ i then .var (.inl i) else (Expr.var (.inl i)).neg

theorem eval_literal {d : ℕ} (σ ρ : Fin d → Bool) (i : Fin d) :
    (literal σ i).eval (grounded ρ)=decide (ρ i=σ i) := by
  cases hx : σ i <;> cases hy : ρ i <;> simp [literal,eval,grounded,hx,hy]

def assignmentExpr {d : ℕ} (σ : Fin d → Bool) : Expr (Fin d ⊕ Bool) := allExpr (List.ofFn (literal σ))

theorem eval_assignmentExpr {d : ℕ} (σ ρ : Fin d → Bool) :
    (assignmentExpr σ).eval (grounded ρ)=decide (ρ=σ) := by
  apply Bool.eq_iff_iff.mpr
  simp only [assignmentExpr,eval_allExpr,List.all_eq_true,decide_eq_true_eq]
  constructor
  · intro h
    funext i
    have hi := h (literal σ i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa only [eval_literal,decide_eq_true_eq] using hi
  · intro he e helem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp helem
    simp [eval_literal,he]

/-- Literal DNF construction from a fixed finite truth table, expanded solely
into NOR syntax and grounded input wires. -/
def truthTable {d : ℕ} (f : (Fin d → Bool) → Bool) : Expr (Fin d ⊕ Bool) :=
  anyExpr (((Finset.univ.filter (fun σ => f σ=true)).toList).map assignmentExpr)

theorem eval_truthTable {d : ℕ} (f : (Fin d → Bool) → Bool) (ρ : Fin d → Bool) :
    (truthTable f).eval (grounded ρ)=f ρ := by
  apply Bool.eq_iff_iff.mpr
  simp only [truthTable,eval_anyExpr,List.any_eq_true,List.mem_map]
  constructor
  · rintro ⟨e,⟨σ,hσ,rfl⟩,he⟩
    have hρ : ρ=σ := by simpa only [eval_assignmentExpr,decide_eq_true_eq] using he
    subst ρ
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hσ)).2
  · intro h
    exact ⟨assignmentExpr ρ,⟨ρ,Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩),rfl⟩,
      by simp [eval_assignmentExpr]⟩

/-- A fixed finite truth table has a genuine shared-register circuit emitter.
The grounding wires are ordinary explicitly indexed inputs to that emitter. -/
theorem fp_truthTable {d : ℕ} (f : (Fin d → Bool) → Bool) :
    let e := (truthTable f).rename (Fintype.equivFin (Fin d ⊕ Bool))
    Complexity.FP (templateInputEncoding (Fintype.card (Fin d ⊕ Bool)))
      ((Complexity.BitEncoding.nat.prod Complexity.BitEncoding.nat).list.prod Complexity.BitEncoding.nat)
      (fun p => (e.emit p.1 p.2,e.output p.1 p.2)) := by
  exact Expr.fp_compile _

end Expr
end PlanarHom.CountingCookLevin
