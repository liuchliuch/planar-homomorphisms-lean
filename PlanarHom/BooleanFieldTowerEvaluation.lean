import PlanarHom.BooleanFieldTower
import Mathlib.Tactic.Linarith

/-! Real sign evaluations of the represented radical algebra. Injectivity uses
all signs and nonzero radical values, including square/dependent radicands;
no field property of the represented algebra is assumed. -/
noncomputable section
namespace PlanarHom.BooleanFieldTowerEvaluation
open BooleanFieldTower
variable {K : Type} [CommRing K]

def eval (f : K→+*ℝ) (r : ℕ→ℝ) : (n : ℕ)→Tower K n→(Fin n→Bool)→ℝ
  | 0,p,_=>f p
  | n+1,p,σ=>eval f r n p.1 (fun i=>σ i.castSucc)+
    (if σ (Fin.last n) then -(r n) else r n)*eval f r n p.2 (fun i=>σ i.castSucc)

@[simp] theorem eval_zero (f : K→+*ℝ) (r : ℕ→ℝ) (n : ℕ) (σ : Fin n→Bool) :
    eval f r n (zero n) σ=0 := by
  induction n with
  | zero=>exact f.map_zero
  | succ n ih=>simp [eval,zero,ih]

@[simp] theorem eval_embed (f : K→+*ℝ) (r : ℕ→ℝ) (n : ℕ) (a : K) (σ : Fin n→Bool) :
    eval f r n (embed n a) σ=f a := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp [eval,embed,ih]

@[simp] theorem eval_add (f : K→+*ℝ) (r : ℕ→ℝ) (n : ℕ) (p q : Tower K n) (σ : Fin n→Bool) :
    eval f r n (add n p q) σ=eval f r n p σ+eval f r n q σ := by
  induction n with
  | zero=>exact f.map_add p q
  | succ n ih=>simp only [eval,add,ih]; ring

@[simp] theorem eval_neg (f : K→+*ℝ) (r : ℕ→ℝ) (n : ℕ) (p : Tower K n) (σ : Fin n→Bool) :
    eval f r n (neg n p) σ= -eval f r n p σ := by
  induction n with
  | zero=>exact f.map_neg p
  | succ n ih=>simp only [eval,neg,ih]; ring

@[simp] theorem eval_sub (f : K→+*ℝ) (r : ℕ→ℝ) (n : ℕ) (p q : Tower K n) (σ : Fin n→Bool) :
    eval f r n (sub n p q) σ=eval f r n p σ-eval f r n q σ := by
  simp [sub,sub_eq_add_neg]

@[simp] theorem eval_mul (f : K→+*ℝ) (r : ℕ→ℝ) (D : ℕ→K)
    (n : ℕ) (hr : ∀i<n,r i^2=f (D i)) (p q : Tower K n) (σ : Fin n→Bool) :
    eval f r n (mul D n p q) σ=eval f r n p σ*eval f r n q σ := by
  induction n with
  | zero=>exact f.map_mul p q
  | succ n ih=>
    have hrl : ∀i<n,r i^2=f (D i):=fun i hi=>hr i (Nat.lt.step hi)
    simp only [mul,eval,eval_add,eval_embed,ih hrl]
    rw [←hr n (Nat.lt_succ_self n)]
    cases σ (Fin.last n) <;> simp only [Bool.false_eq_true,↓reduceIte] <;> ring

@[simp] theorem eval_snoc (f : K→+*ℝ) (r : ℕ→ℝ) (n : ℕ) (p : Tower K (n+1))
    (σ : Fin n→Bool) (b : Bool) :
    eval f r (n+1) p (Fin.snoc σ b)=eval f r n p.1 σ+(if b then -(r n) else r n)*eval f r n p.2 σ := by
  simp [eval]

theorem allSign_injective (f : K→+*ℝ) (hf : Function.Injective f) (r : ℕ→ℝ)
    (n : ℕ) (hr : ∀i<n,r i≠0) : Function.Injective (fun p : Tower K n=>fun σ=>eval f r n p σ) := by
  induction n with
  | zero=>
    intro p q h
    exact hf (congrFun h (fun i=>Fin.elim0 i))
  | succ n ih=>
    intro p q h
    have pair (σ : Fin n→Bool) : eval f r n p.1 σ=eval f r n q.1 σ ∧
        eval f r n p.2 σ=eval f r n q.2 σ := by
      have hp:=congrFun h (Fin.snoc σ false)
      have hm:=congrFun h (Fin.snoc σ true)
      simp only [eval_snoc,Bool.false_eq_true,↓reduceIte] at hp hm
      have hd : r n*(eval f r n p.2 σ-eval f r n q.2 σ)=0 := by linarith
      have hz := (mul_eq_zero.mp hd).resolve_left (hr n (Nat.lt_succ_self n))
      constructor <;> linarith
    have hrl : ∀i<n,r i≠0:=fun i hi=>hr i (Nat.lt.step hi)
    exact Prod.ext (ih hrl (funext (fun σ=>(pair σ).1))) (ih hrl (funext (fun σ=>(pair σ).2)))

theorem eq_embed_of_all_evaluations_eq (f : K→+*ℝ) (hf : Function.Injective f)
    (r : ℕ→ℝ) (n : ℕ) (hr : ∀i<n,r i≠0) (p : Tower K n) (a : K)
    (h : ∀σ,eval f r n p σ=f a) : p=embed n a := by
  apply allSign_injective f hf r n hr
  funext σ
  change eval f r n p σ=eval f r n (embed n a) σ
  rw [h,eval_embed]

theorem eval_norm_ne_zero_iff (f : K→+*ℝ) (r : ℕ→ℝ) (D : ℕ→K)
    (n : ℕ) (hr : ∀i<n,r i^2=f (D i)) (p : Tower K n) :
    f (norm D n p)≠0 ↔ ∀σ,eval f r n p σ≠0 := by
  induction n with
  | zero=>simp [norm,eval]
  | succ n ih=>
    have hrl : ∀i<n,r i^2=f (D i):=fun i hi=>hr i (Nat.lt.step hi)
    rw [norm,ih hrl]
    simp only [eval_sub,eval_mul f r D n hrl,eval_embed]
    have hfactor (σ : Fin n→Bool) :
        eval f r n p.1 σ*eval f r n p.1 σ-f (D n)*(eval f r n p.2 σ*eval f r n p.2 σ)=
        (eval f r n p.1 σ+r n*eval f r n p.2 σ)*(eval f r n p.1 σ-r n*eval f r n p.2 σ) := by
      rw [←hr n (Nat.lt_succ_self n)]
      ring
    simp only [hfactor,mul_ne_zero_iff]
    constructor
    · intro h σ
      have hh:=h (fun i=>σ i.castSucc)
      cases hb:σ (Fin.last n)
      · simpa [eval,hb] using hh.1
      · simpa [eval,hb,sub_eq_add_neg] using hh.2
    · intro h σ
      have hp:=h (Fin.snoc σ false)
      have hm:=h (Fin.snoc σ true)
      simpa only [eval_snoc,Bool.false_eq_true,↓reduceIte,neg_mul,←sub_eq_add_neg] using And.intro hp hm

end PlanarHom.BooleanFieldTowerEvaluation
