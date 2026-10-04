import PlanarHom.DensePolynomialSemantics

/-! The materialized convolution machine computes genuine polynomial products.
This bridge handles recursive dense coefficient codes without pretending those
noncanonical lists themselves form a field or ring. -/
noncomputable section
namespace PlanarHom.DensePolynomial

private theorem zipIdx_map {A B : Type} (f:A→B) (xs:List A) (k:ℕ) :
    (xs.map f).zipIdx k=(xs.zipIdx k).map (fun p=>(f p.1,p.2)) := by
  induction xs generalizing k with
  | nil => rfl
  | cons a xs ih => simp [List.zipIdx_cons,ih]

private theorem lookup_map {A R : Type} [Zero R] (f:A→R) (z:A) (hz:f z=0)
    (xs:List A) (k:ℕ) : (xs.map f)[k]?.getD 0=f (xs[k]?.getD z) := by
  rw [List.getElem?_map]
  cases xs[k]? <;> simp [hz]

private theorem convolution_map {A R : Type} [CommRing R]
    (z:A) (mulA:A→A→A) (sumA:List A→A) (f:A→R)
    (hz:f z=0) (hm:∀a b,f (mulA a b)=f a*f b)
    (hs:∀xs,f (sumA xs)=(xs.map f).sum) (a b:List A) :
    (CoefficientConvolutionMachines.convolution z (fun _:ℕ=>mulA) (fun _:ℕ=>sumA) (0,(a,b))).map f=
      CoefficientListAlgebra.convolution (a.map f) (b.map f) := by
  unfold CoefficientConvolutionMachines.convolution CoefficientListAlgebra.convolution
  simp only [List.map_map,List.length_map]
  apply List.map_congr_left
  intro k hk
  unfold CoefficientConvolutionMachines.coefficient CoefficientListAlgebra.convolutionCoefficient
  dsimp only [Function.comp_apply]
  rw [hs]
  simp only [List.map_map,zipIdx_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases h:k<p.2
  · simp [CoefficientConvolutionMachines.term,h,hz]
  · simp only [CoefficientConvolutionMachines.term,h,↓reduceIte,hm]
    rw [lookup_map f z hz]

theorem interpret_mul (n:ℕ) (a b:Code n) :
    interpret n (mul n a b)=interpret n a*interpret n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change CoefficientListAlgebra.polynomial
      ((CoefficientConvolutionMachines.convolution (zero n) (fun _:ℕ=>mul n)
        (fun _:ℕ=>sum n) (0,(a,b))).map (interpret n))=
      CoefficientListAlgebra.polynomial (a.map (interpret n))*
        CoefficientListAlgebra.polynomial (b.map (interpret n))
    rw [convolution_map (zero n) (mul n) (sum n) (interpret n) (interpret_zero n)
      ih (interpret_sum n)]
    exact CoefficientListAlgebra.convolution_polynomial _ _

theorem interpret_neg (n:ℕ) (a:Code n) : interpret n (neg n a)= -interpret n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Polynomial.ext
    intro k
    rw [interpret_coeff,Polynomial.coeff_neg,interpret_coeff]
    have hg : (neg (n+1) a)[k]?=(a[k]?).map (neg n) := by
      change (a.map (neg n))[k]?=_
      rw [List.getElem?_map]
    rw [hg]
    cases h:a[k]? <;> simp [ih,interpret_zero]

theorem interpret_add (n:ℕ) (a b:Code n) :
    interpret n (add n a b)=interpret n a+interpret n b := by
  rw [add,interpret_sum]
  simp

/-- Cross-product equality testing compares genuine polynomial identities,
including every trailing-zero representation. -/
theorem fractionEq_iff (n:ℕ) (a b:FractionCode n) :
    fractionEq n a b=true ↔
      interpret n a.1*interpret n b.2=interpret n b.1*interpret n a.2 := by
  rw [fractionEq,isZero_iff,interpret_add,interpret_mul,interpret_neg,interpret_mul]
  exact add_neg_eq_zero

end PlanarHom.DensePolynomial
