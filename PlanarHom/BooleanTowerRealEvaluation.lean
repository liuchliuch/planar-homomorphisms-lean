import PlanarHom.BooleanTowerSpectral
import PlanarHom.BooleanEffectiveLengthSamples

/-! All real sign evaluations of the represented spectral nodes. Positivity
holds for every sign, so node invertibility never relies on only the principal
square-root specialization. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanTowerRealEvaluation
open BooleanFieldTower BooleanFieldTowerAlgebra BooleanFieldTowerEvaluation
open BooleanFieldTowerReconstruction BooleanFieldCollision
variable {K : Type} [Field K] {b : ℕ}

theorem eval_linear (f:K→+*ℝ) (r:ℕ→ℝ) (n:ℕ) (i:Fin n) (e o:K) (σ:Fin n→Bool) :
    eval f r n (linear n i e o) σ=f e+(if σ i then -r i.val else r i.val)*f o := by
  induction n with
  | zero=>exact Fin.elim0 i
  | succ n ih=>
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp [linear,eval]
    · simp [linear,eval,ih]

def roots (f:K→+*ℝ) (a w:Fin b→K) (x:K) (i:ℕ) : ℝ:=Real.sqrt (f (radicands a w x i))

theorem roots_square (f:K→+*ℝ) (a w:Fin b→K) (x:K) (i:ℕ) :
    roots f a w x i^2=f (radicands a w x i) := by
  apply Real.sq_sqrt
  simp only [radicands,_root_.map_add,_root_.map_mul,_root_.map_pow]
  positivity

theorem roots_val (f:K→+*ℝ) (a w:Fin b→K) (x:K) (i:Fin b) :
    roots f a w x i.val=Real.sqrt ((f (a i))^2+(f (w i))^2*(f x)^2) := by
  simp [roots,radicands]

theorem eval_spectral (f:K→+*ℝ) (c a w:Fin b→K) (x:K) (n k:Fin b→ℕ) (σ:Fin b→Bool) :
    eval f (roots f a w x) b (spectral c a w x n k) σ=
      BooleanConjugateProducts.spectralProduct Finset.univ (fun i=>f (c i))
        (fun i=>f (a i)) (fun i=>f (w i)) n k σ (f x) := by
  let D:=radicands a w x
  let e:=evalHom f (roots f a w x) D b (fun i _=>roots_square f a w x i) σ
  change e (spectral c a w x n k)=_
  let p : Fin b→Carrier D b:=fun i=>linear b i (c i) 1
  let v : Fin b→Carrier D b:=fun i=>linear b i (c i) (-1)
  have hs : @Eq (Carrier D b) (spectral c a w x n k)
      (∏i,(p i)^(n i-k i)*(v i)^(k i)) := by
    simp only [product_eq,mul_eq,pow_eq,spectral,D,p,v]
  rw [hs]
  rw [_root_.map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [_root_.map_mul,_root_.map_pow]
  change (eval f (roots f a w x) b (linear b i (c i) 1) σ)^(n i-k i)*
      (eval f (roots f a w x) b (linear b i (c i) (-1)) σ)^(k i)=_
  rw [eval_linear,eval_linear]
  simp only [_root_.map_one,_root_.map_neg,mul_one,mul_neg,roots_val]
  rw [BooleanConjugateProducts.signedBranch_eq_add_signedRoot,
    BooleanConjugateProducts.signedBranch_not_eq_sub_signedRoot]
  simp only [sub_eq_add_neg]

/-- Every represented source product has nonzero algebra norm on the actual
oracle interval, even when radicands are squares or repeated. -/
theorem norm_spectral_ne_zero (f:K→+*ℝ) (c a w:Fin b→K) (x:K) (n k:Fin b→ℕ)
    (hp:BooleanExceptionalSource.SeparatedParameters
      (fun i=>f (c i)) (fun i=>f (a i)) (fun i=>f (w i)))
    (hx:f x∈Set.Ioo (0:ℝ) 1) :
    norm (radicands a w x) b (spectral c a w x n k)≠0 := by
  apply norm_ne_zero_of_all_evaluations_ne_zero f (roots f a w x)
    (radicands a w x) b (fun i _=>roots_square f a w x i)
  intro σ
  rw [eval_spectral]
  exact ne_of_gt (BooleanConjugateProducts.spectralProduct_pos Finset.univ
    (fun i=>f (c i)) (fun i=>f (a i)) (fun i=>f (w i)) n k σ (f x)
    (fun i _=>hp.c_pos i) (fun i _=>hp.parameter_eq i)
    (fun i _=>hp.w_pos i) (fun i _=>hp.w_lt_one i) hx)

end PlanarHom.BooleanTowerRealEvaluation
