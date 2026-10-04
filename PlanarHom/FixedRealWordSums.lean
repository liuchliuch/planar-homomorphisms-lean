import PlanarHom.FixedRealAlphabetBounds

/-! NEW existence construction for sums of equal-length fixed-alphabet words.
All coordinate numerators are summed over one literal polynomial denominator;
the independent rational coefficient clearing factor is retained in the bounds. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealWordSums
open DensePolynomial FixedRealAlphabet
variable {n e t:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable {basis:Module.Basis (Fin e) (RationalFunction n) K} {A:Fin t→K}

 def denominatorAt (d:Data basis A) : ℕ→Code n
  | 0=>d.denominator
  | L+1=>mul n d.denominator (denominatorAt d L)

 theorem denominatorAt_value (d:Data basis A) (L:ℕ) :
    interpret n (denominatorAt d L)=(interpret n d.denominator)^(L+1) := by
  induction L with
  | zero=>simp [denominatorAt]
  | succ L ih=>
    rw [denominatorAt,interpret_mul,ih]
    exact (pow_succ' _ (L+1)).symm

 theorem denominatorAt_valid (d:Data basis A) (L:ℕ) : interpret n (denominatorAt d L)≠0 := by
  rw [denominatorAt_value]
  exact pow_ne_zero _ d.valid

 theorem fold_denominator (d:Data basis A) (xs:List (Fin t)) (L:ℕ)
    (s:FixedRealExtension.Code n e) (hs:s.2=denominatorAt d L) :
    (xs.foldl (step d) s).2=denominatorAt d (L+xs.length) := by
  induction xs generalizing L s with
  | nil=>simpa using hs
  | cons a xs ih=>
    rw [List.foldl_cons]
    have hh:(step d s a).2=denominatorAt d (L+1):=by simp only [step,denominatorAt,hs]
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (L+1) _ hh

 theorem word_denominator (d:Data basis A) (xs:List (Fin t)) :
    (word d xs).2=denominatorAt d xs.length := by
  simpa only [word,Nat.zero_add] using fold_denominator d xs 0 (initial d) rfl

 def sumWords (d:Data basis A) (L:ℕ) (words:List (List (Fin t))) : FixedRealExtension.Code n e :=
    (fun i=>sum n (words.map (fun xs=>(word d xs).1 i)),denominatorAt d L)

 theorem sumWords_valid (d:Data basis A) (L:ℕ) (words:List (List (Fin t))) :
    FixedRealExtension.Valid n (sumWords d L words) := denominatorAt_valid d L

 theorem list_sum_apply {I R:Type} [AddCommMonoid R] (xs:List (I→R)) (i:I) :
    xs.sum i=(xs.map (fun f=>f i)).sum := by
  induction xs with
  | nil=>rfl
  | cons f xs ih=>simp [ih]

 theorem list_sum_div (xs:List K) (c:K) : xs.sum/c=(xs.map (fun x=>x/c)).sum := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>simp [add_div,ih]

 theorem sumWords_value (d:Data basis A) (L:ℕ) (words:List (List (Fin t)))
    (hlen:∀xs∈words,xs.length=L) :
    FixedRealExtension.value basis (sumWords d L words)=(words.map (fun xs=>(xs.map A).prod)).sum := by
  apply basis.equivFun.injective
  rw [FixedRealExtension.value,basis.equivFun.apply_symm_apply,map_list_sum]
  funext i
  simp only [FixedRealExtension.coordinates,sumWords,fractionValue,interpret_sum,map_list_sum,
    List.map_map,Function.comp_def,list_sum_apply]
  rw [list_sum_div]
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro xs hxs
  have hv:=congrArg (fun x=>basis.equivFun x i) (word_value d xs)
  have he:(word d xs).2=denominatorAt d L:=(word_denominator d xs).trans (congrArg (denominatorAt d) (hlen xs hxs))
  simpa only [FixedRealExtension.value,basis.equivFun.apply_symm_apply,FixedRealExtension.coordinates,
    fractionValue,he] using hv

 theorem denominatorAt_bound (d:Data basis A) (b:Bounds d) (L:ℕ) :
    BoxBound n ((b.W+1)*(L+1)) (denominatorAt d L) ∧
      CoeffBound n (b.D^(L+1)) (b.C^(L+1)) (denominatorAt d L) := by
  induction L with
  | zero=>exact (initial_bound d b).1
  | succ L ih=>
    have hg:b.W^n*b.H≤b.C := by
      have he:b.W^n*b.H≤(e+1)*b.W^n*b.H:=by
        simpa only [one_mul,Nat.mul_assoc] using Nat.mul_le_mul_right (b.W^n*b.H) (show 1≤e+1 by omega)
      exact he.trans b.factor_le_C
    constructor
    · have hw:=box_mul n b.W ((b.W+1)*(L+1)) d.denominator (denominatorAt d L) b.denominator.1 ih.1
      have he:b.W+(b.W+1)*(L+1)+1=(b.W+1)*(L+1+1):=by ring
      simpa only [denominatorAt,he] using hw
    · have hc:=coeff_mul n b.W ((b.W+1)*(L+1)) b.D (b.D^(L+1)) b.H (b.C^(L+1))
        d.denominator (denominatorAt d L) b.denominator.1 ih.1 b.denominator.2 ih.2
      have hh:b.W^n*b.H*b.C^(L+1)≤b.C^(L+1+1):=by
        calc
          _ ≤ b.C*b.C^(L+1):=Nat.mul_le_mul_right _ hg
          _ = b.C^(L+1+1):=(pow_succ' _ _).symm
      have hd:b.D*b.D^(L+1)=b.D^(L+1+1):=(pow_succ' _ _).symm
      simpa only [denominatorAt,hd] using coeff_mono n _ hh hc

end PlanarHom.FixedRealWordSums
