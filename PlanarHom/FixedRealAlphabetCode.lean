import PlanarHom.FixedRealExtensionCompleteness
import PlanarHom.DensePolynomialFixedBounds
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Fixed-alphabet products are evaluated by a cleared polynomial matrix
recurrence. Each step uses one fixed common polynomial denominator, once.
These are literal dense-code functions, not abstract field-operation oracles. -/
noncomputable section
open scoped BigOperators Matrix
namespace PlanarHom.FixedRealAlphabet
open DensePolynomial
variable {n e t:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

def multiplicationMatrix (basis:Module.Basis (Fin e) (RationalFunction n) K) (x:K) :
    Matrix (Fin e) (Fin e) (RationalFunction n) :=
  LinearMap.toMatrix basis basis (LinearMap.mulRight (RationalFunction n) x)

theorem multiplicationMatrix_mulVec (basis:Module.Basis (Fin e) (RationalFunction n) K) (a x:K) :
    multiplicationMatrix basis a *ᵥ basis.equivFun x=basis.equivFun (x*a) := by
  simpa only [multiplicationMatrix,Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr basis basis (LinearMap.mulRight (RationalFunction n) a) x

structure Data (basis:Module.Basis (Fin e) (RationalFunction n) K) (A:Fin t→K) where
  denominator : Code n
  initial : Fin e→Code n
  transition : Fin t→Fin e→Fin e→Code n
  valid : interpret n denominator≠0
  initial_value : ∀i,fractionValue n (initial i,denominator)=basis.equivFun 1 i
  transition_value : ∀a i j,fractionValue n (transition a i j,denominator)=multiplicationMatrix basis (A a) i j

theorem exists_data (basis:Module.Basis (Fin e) (RationalFunction n) K) (A:Fin t→K) :
    Nonempty (Data basis A) := by
  let f:(Fin e⊕Fin t×Fin e×Fin e)→RationalFunction n
    | .inl i=>basis.equivFun 1 i
    | .inr p=>multiplicationMatrix basis (A p.1) p.2.1 p.2.2
  obtain ⟨d,p,hd,hp⟩:=exists_common_denominator n f
  exact ⟨⟨d,fun i=>p (.inl i),fun a i j=>p (.inr (a,i,j)),hd,
    fun i=>hp (.inl i),fun a i j=>hp (.inr (a,i,j))⟩⟩

def data (basis:Module.Basis (Fin e) (RationalFunction n) K) (A:Fin t→K) : Data basis A :=
  Classical.choice (exists_data basis A)

variable {basis:Module.Basis (Fin e) (RationalFunction n) K} {A:Fin t→K}

def initial (d:Data basis A) : FixedRealExtension.Code n e := (d.initial,d.denominator)

def step (d:Data basis A) (s:FixedRealExtension.Code n e) (a:Fin t) : FixedRealExtension.Code n e :=
  (fun i=>fixedSum n e (fun j=>mul n (d.transition a i j) (s.1 j)),mul n d.denominator s.2)

def word (d:Data basis A) (xs:List (Fin t)) : FixedRealExtension.Code n e :=
  xs.foldl (step d) (initial d)

theorem step_valid (d:Data basis A) (s:FixedRealExtension.Code n e) (hs:FixedRealExtension.Valid n s) (a:Fin t) :
    FixedRealExtension.Valid n (step d s a) := by
  change interpret n (mul n d.denominator s.2)≠0
  rw [interpret_mul]
  exact mul_ne_zero d.valid hs

theorem step_coordinates (d:Data basis A) (s:FixedRealExtension.Code n e) (a:Fin t) :
    FixedRealExtension.coordinates n (step d s a)=multiplicationMatrix basis (A a) *ᵥ FixedRealExtension.coordinates n s := by
  funext i
  simp only [FixedRealExtension.coordinates,step,fractionValue,interpret_fixedSum,interpret_mul,
    map_sum,map_mul,Finset.sum_div,Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j hj
  rw [←d.transition_value a i j]
  simp only [fractionValue,div_eq_mul_inv,mul_inv_rev]
  ring

theorem value_step (d:Data basis A) (s:FixedRealExtension.Code n e) (a:Fin t) :
    FixedRealExtension.value basis (step d s a)=FixedRealExtension.value basis s*A a := by
  apply basis.equivFun.injective
  rw [FixedRealExtension.value,basis.equivFun.apply_symm_apply,step_coordinates]
  have he:FixedRealExtension.coordinates n s=basis.equivFun (FixedRealExtension.value basis s) :=
    (basis.equivFun.apply_symm_apply _).symm
  rw [he,multiplicationMatrix_mulVec]

theorem initial_value (d:Data basis A) : FixedRealExtension.value basis (initial d)=1 := by
  apply basis.equivFun.injective
  rw [FixedRealExtension.value,basis.equivFun.apply_symm_apply]
  exact funext d.initial_value

theorem value_fold (d:Data basis A) (xs:List (Fin t)) (s:FixedRealExtension.Code n e) :
    FixedRealExtension.value basis (xs.foldl (step d) s)=FixedRealExtension.value basis s*(xs.map A).prod := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih => simp only [List.foldl_cons,ih,value_step,List.map_cons,List.prod_cons,mul_assoc]

theorem word_value (d:Data basis A) (xs:List (Fin t)) :
    FixedRealExtension.value basis (word d xs)=(xs.map A).prod := by
  rw [word,value_fold,initial_value,one_mul]

theorem word_valid (d:Data basis A) (xs:List (Fin t)) : FixedRealExtension.Valid n (word d xs) := by
  have h:∀s:FixedRealExtension.Code n e,FixedRealExtension.Valid n s→
      FixedRealExtension.Valid n (xs.foldl (step d) s) := by
    induction xs with
    | nil => exact fun _ hs=>hs
    | cons a xs ih => exact fun s hs=>ih _ (step_valid d s hs a)
  exact h _ d.valid

end PlanarHom.FixedRealAlphabet
