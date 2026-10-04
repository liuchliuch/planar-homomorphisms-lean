import PlanarHom.ParsimoniousNorCompiler

/-! A shared-register NOR straight-line compiler. Expression trees are local
finite templates; emitted gates reference old registers instead of recursively
substituting earlier time layers. -/
namespace PlanarHom.CountingCookLevin
open ParsimoniousNorOneInThree

inductive Expr (V : Type) where
  | var (v : V)
  | nor (a b : Expr V)

namespace Expr

def eval {V : Type} (ρ : V → Bool) : Expr V → Bool
  | .var v => ρ v
  | .nor a b => !(a.eval ρ || b.eval ρ)

def gates {V : Type} : Expr V → ℕ
  | .var _ => 0
  | .nor a b => a.gates+b.gates+1

def output {V : Type} : Expr V → ℕ → (V → ℕ) → ℕ
  | .var v, _, ρ => ρ v
  | .nor a b, start, _ => start+4*(a.gates+b.gates)

def emit {V : Type} : Expr V → ℕ → (V → ℕ) → List (ℕ × ℕ)
  | .var _, _, _ => []
  | .nor a b, start, ρ =>
      a.emit start ρ ++ b.emit (start+4*a.gates) ρ ++
        [(a.output start ρ,b.output (start+4*a.gates) ρ)]

theorem emit_length {V : Type} (e : Expr V) (start : ℕ) (ρ : V → ℕ) :
    (e.emit start ρ).length=e.gates := by
  induction e generalizing start with
  | var v => rfl
  | nor a b ha hb => simp [emit,gates,ha,hb,Nat.add_assoc]

theorem output_bound {V : Type} (e : Expr V) (start : ℕ) (ρ : V → ℕ)
    (hρ : ∀ v, ρ v<start) : e.output start ρ<start+4*e.gates := by
  cases e with
  | var v => simpa [output,gates] using hρ v
  | nor a b => simp only [output,gates]; omega

theorem eval_congr {V : Type} (e : Expr V) (ρ τ : V → Bool) (h : ∀ v,ρ v=τ v) :
    e.eval ρ=e.eval τ := by
  induction e with
  | var v => exact h v
  | nor a b ha hb => simp only [eval,ha,hb]

end Expr

abbrev NorGates := List (ℕ × ℕ)

def readBit (xs : List Bool) (i : ℕ) : Bool := xs[i]?.getD false

def norStep (xs : List Bool) (p : ℕ × ℕ) : List Bool :=
  xs ++ List.ofFn (extension (readBit xs p.1) (readBit xs p.2))

def runNor (gs : NorGates) (xs : List Bool) : List Bool := gs.foldl norStep xs

@[simp] theorem norStep_length (xs : List Bool) (p : ℕ × ℕ) :
    (norStep xs p).length=xs.length+4 := by simp [norStep]

@[simp] theorem runNor_nil (xs : List Bool) : runNor [] xs=xs := rfl
@[simp] theorem runNor_single (xs : List Bool) (p : ℕ × ℕ) : runNor [p] xs=norStep xs p := rfl
@[simp] theorem runNor_append (gs hs : NorGates) (xs : List Bool) :
    runNor (gs++hs) xs=runNor hs (runNor gs xs) := List.foldl_append

@[simp] theorem runNor_length (gs : NorGates) (xs : List Bool) :
    (runNor gs xs).length=xs.length+4*gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons p gs ih =>
    change (runNor gs (norStep xs p)).length=_
    rw [ih,norStep_length,List.length_cons]
    omega

theorem norStep_read_old (xs : List Bool) (p : ℕ × ℕ) (i : ℕ) (hi : i<xs.length) :
    readBit (norStep xs p) i=readBit xs i := by
  simp only [readBit,norStep,List.getElem?_append_left hi]

theorem runNor_read_old (gs : NorGates) (xs : List Bool) (i : ℕ) (hi : i<xs.length) :
    readBit (runNor gs xs) i=readBit xs i := by
  induction gs generalizing xs with
  | nil => rfl
  | cons p gs ih =>
    change readBit (runNor gs (norStep xs p)) i=_
    rw [ih _ (by simp; omega),norStep_read_old xs p i hi]

/-- The first fresh register stores NOR; all additional registers are the same
unique auxiliary extension used by the positive one-in-three gadget. -/
theorem norStep_read_output (xs : List Bool) (i j : ℕ) :
    readBit (norStep xs (i,j)) xs.length= !(readBit xs i || readBit xs j) := by
  simp [readBit,norStep,List.getElem?_append_right (le_refl xs.length),extension,List.ofFn_succ]

/-- Exact correctness of the emitted shared-register circuit for every local
expression template. Fresh registers are allocated from the actual store length. -/
theorem Expr.emit_correct {V : Type} (e : Expr V) (ρ : V → ℕ) (xs : List Bool)
    (hρ : ∀ v,ρ v<xs.length) :
    readBit (runNor (e.emit xs.length ρ) xs) (e.output xs.length ρ)=
      e.eval (fun v => readBit xs (ρ v)) := by
  induction e generalizing xs with
  | var v => rfl
  | nor a b ha hb =>
    let xa := runNor (a.emit xs.length ρ) xs
    let xab := runNor (b.emit xa.length ρ) xa
    have hla : xa.length=xs.length+4*a.gates := by simp [xa,Expr.emit_length]
    have hlah : xs.length≤xa.length := by omega
    have hlav : ∀ v,ρ v<xa.length := fun v => (hρ v).trans_le hlah
    have hlab : xab.length=xs.length+4*(a.gates+b.gates) := by
      simp only [xab,runNor_length,Expr.emit_length,hla]
      omega
    have hau : a.output xs.length ρ < xa.length := by
      rw [hla]
      exact a.output_bound _ _ hρ
    have hra : readBit xab (a.output xs.length ρ)=a.eval (fun v => readBit xs (ρ v)) := by
      rw [show readBit xab (a.output xs.length ρ)=readBit xa (a.output xs.length ρ) from
        runNor_read_old _ xa _ hau]
      exact ha xs hρ
    have hrb : readBit xab (b.output xa.length ρ)=b.eval (fun v => readBit xs (ρ v)) := by
      rw [show readBit xab (b.output xa.length ρ)=b.eval (fun v => readBit xa (ρ v)) from hb xa hlav]
      exact b.eval_congr _ _ (fun v => runNor_read_old _ xs _ (hρ v))
    simp only [Expr.emit,Expr.output,runNor_append,runNor_single]
    rw [← hla]
    change readBit (norStep xab (a.output xs.length ρ,b.output xa.length ρ))
      (xs.length+4*(a.gates+b.gates))=_
    rw [← hlab,norStep_read_output,hra,hrb]
    rfl

end PlanarHom.CountingCookLevin
