import PlanarHom.OccurrenceKasteleynPeeling
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-! NEW literal occurrence boundary signs, using the recovered convention.
Agreement with the traversed dart contributes +1, disagreement contributes −1.
The exact connection to the executable face-parity predicate is proved. -/
namespace PlanarHom.MultiGraph.Kasteleyn
variable {E : Type*}

def dartSign (orientation : E → Bool) (a : Dart E) : ℤ :=
  if orientation a.1=a.2 then 1 else -1

def boundarySign (orientation : E → Bool) (ds : List (Dart E)) : ℤ :=
  (ds.map (dartSign orientation)).prod

def bitSign (b : Bool) : ℤ := if b then -1 else 1

theorem bitSign_xor (b c : Bool) : bitSign (b ^^ c)=bitSign b*bitSign c := by
  cases b <;> cases c <;> norm_num [bitSign]

theorem bitSign_not (b : Bool) : bitSign (!b)= -bitSign b := by cases b <;> norm_num [bitSign]

theorem bitSign_bodd (n : ℕ) : bitSign n.bodd=(-1:ℤ)^n := by
  induction n with
  | zero => norm_num [bitSign]
  | succ n ih => rw [Nat.bodd_succ,bitSign_not,ih,pow_succ]; ring

theorem dartSign_eq_bitSign (orientation : E → Bool) (a : Dart E) :
    dartSign orientation a=bitSign (orientation a.1 ^^ a.2) := by
  cases ho : orientation a.1 <;> cases ha : a.2 <;> simp [dartSign,bitSign,ho,ha]

@[simp] theorem boundarySign_nil (orientation : E → Bool) : boundarySign orientation []=1 := rfl
@[simp] theorem boundarySign_cons (orientation : E → Bool) (a : Dart E) (ds : List (Dart E)) :
    boundarySign orientation (a::ds)=dartSign orientation a*boundarySign orientation ds := rfl
@[simp] theorem boundarySign_append (orientation : E → Bool) (xs ys : List (Dart E)) :
    boundarySign orientation (xs++ys)=boundarySign orientation xs*boundarySign orientation ys := by
  simp [boundarySign]

theorem boundarySign_parity (orientation : E → Bool) (ds : List (Dart E)) :
    boundarySign orientation ds=bitSign (boundaryParity orientation ds) := by
  induction ds with
  | nil => rfl
  | cons a ds ih => rw [boundarySign_cons,boundaryParity_cons,bitSign_xor,←dartSign_eq_bitSign,←ih]

theorem faceTarget_sign (ds : List (Dart E)) : bitSign (faceTarget ds)=(-1:ℤ)^(ds.length+1) := by
  rw [faceTarget,←Nat.bodd_succ,bitSign_bodd]

theorem FaceOdd.boundarySign {orientation : E → Bool} {ds : List (Dart E)} (h : FaceOdd orientation ds) :
    boundarySign orientation ds=(-1:ℤ)^(ds.length+1) := by
  rw [boundarySign_parity,h,faceTarget_sign]

@[simp] theorem dartSign_sq (orientation : E → Bool) (a : Dart E) : dartSign orientation a^2=1 := by
  unfold dartSign
  split_ifs <;> norm_num

theorem boundarySign_sq (orientation : E → Bool) (ds : List (Dart E)) : boundarySign orientation ds^2=1 := by
  induction ds with
  | nil => simp
  | cons a ds ih => rw [boundarySign_cons,mul_pow,dartSign_sq,ih,mul_one]

theorem dartSign_reverse (orientation : E → Bool) (a : Dart E) :
    dartSign orientation (a.1,!a.2)= -dartSign orientation a := by
  cases ho : orientation a.1 <;> cases ha : a.2 <;> simp [dartSign,ho,ha]

theorem opposite_dart_product (orientation : E → Bool) (a : Dart E) :
    dartSign orientation a*dartSign orientation (a.1,!a.2)= -1 := by
  rw [dartSign_reverse,mul_neg,←pow_two,dartSign_sq]

theorem boundarySign_perm (orientation : E → Bool) {xs ys : List (Dart E)} (h : xs.Perm ys) :
    boundarySign orientation xs=boundarySign orientation ys := (h.map (dartSign orientation)).prod_eq

end PlanarHom.MultiGraph.Kasteleyn
