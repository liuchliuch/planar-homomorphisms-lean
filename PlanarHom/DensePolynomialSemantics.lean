import PlanarHom.DensePolynomialCode

/-! Dense codes represent genuine iterated polynomial rings over Q.
Trailing zero padding is semantically irrelevant, and zero testing is exact.
No evaluation of a transcendental real number appears in these statements. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.DensePolynomial

def polyBundle : ℕ→ΣR:Type,CommRing R
  | 0 => ⟨ℚ,inferInstance⟩
  | n+1 => let B:=polyBundle n; letI:=B.2; ⟨Polynomial B.1,inferInstance⟩

abbrev Poly (n:ℕ) := (polyBundle n).1
instance (n:ℕ) : CommRing (Poly n) := (polyBundle n).2

def interpret : (n:ℕ)→Code n→Poly n
  | 0,a => a
  | n+1,a => CoefficientListAlgebra.polynomial (a.map (interpret n))

@[simp] theorem interpret_zero (n:ℕ) : interpret n (zero n)=0 := by
  cases n <;> rfl

private theorem lookup_map {A R : Type} [Zero R] (f:A→R) (z:A) (hz:f z=0)
    (xs:List A) (k:ℕ) : (xs.map f)[k]?.getD 0=f (xs[k]?.getD z) := by
  rw [List.getElem?_map]
  cases xs[k]? <;> simp [hz]

theorem interpret_coeff (n:ℕ) (xs:Code (n+1)) (k:ℕ) :
    (interpret (n+1) xs).coeff k=interpret n (xs[k]?.getD (zero n)) := by
  rw [interpret,CoefficientListAlgebra.polynomial_coeff]
  exact lookup_map _ _ (interpret_zero n) xs k

private theorem coeff_list_sum {R : Type} [Semiring R] (ps:List (Polynomial R)) (k:ℕ) :
    ps.sum.coeff k=(ps.map (fun p=>p.coeff k)).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih]

theorem interpret_sum (n:ℕ) (xs:List (Code n)) :
    interpret n (sum n xs)=(xs.map (interpret n)).sum := by
  induction n with
  | zero => simp [interpret,sum]
  | succ n ih =>
    apply Polynomial.ext
    intro k
    rw [interpret_coeff,coeff_list_sum]
    simp only [List.map_map,Function.comp_def]
    by_cases hk:k<width xs
    · have hget : (sum (n+1) xs)[k]?=some (sum n (gather (zero n) k xs)) := by
        change ((List.range (width xs)).map (fun j=>sum n (gather (zero n) j xs)))[k]?=_
        rw [List.getElem?_map,List.getElem?_range hk]
        rfl
      rw [hget,Option.getD_some,ih]
      simp only [gather,List.map_map,Function.comp_def]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      exact (interpret_coeff n p k).symm
    · have hn : (sum (n+1) xs)[k]?=none := by
        apply List.getElem?_eq_none
        simp only [sum,List.length_map,List.length_range]
        omega
      rw [hn,Option.getD_none,interpret_zero]
      symm
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hz
      rw [interpret_coeff,List.getElem?_eq_none,Option.getD_none,interpret_zero]
      exact (length_le_width xs p hp).trans (Nat.le_of_not_gt hk)

private theorem polynomial_cons_zero_iff {R : Type} [CommRing R] (a:R) (xs:List R) :
    CoefficientListAlgebra.polynomial (a::xs)=0 ↔ a=0 ∧ CoefficientListAlgebra.polynomial xs=0 := by
  constructor
  · intro h
    have hz:=congrArg (fun p:Polynomial R=>p.coeff 0) h
    have hz' : a=0 := by simpa [CoefficientListAlgebra.polynomial] using hz
    refine ⟨hz',?_⟩
    ext k
    have hk:=congrArg (fun p:Polynomial R=>p.coeff (k+1)) h
    simpa [CoefficientListAlgebra.polynomial] using hk
  · rintro ⟨rfl,h⟩
    simp [CoefficientListAlgebra.polynomial,h]

theorem isZero_iff (n:ℕ) (a:Code n) : isZero n a=true ↔ interpret n a=0 := by
  induction n with
  | zero => simp [isZero,interpret]
  | succ n ih =>
    induction a with
    | nil => simp [isZero,interpret,CoefficientListAlgebra.polynomial]
    | cons x xs hs =>
      simp only [isZero,List.any_cons,Bool.not_or,Bool.not_not,Bool.and_eq_true]
      change (isZero n x=true ∧ isZero (n+1) xs=true) ↔
        CoefficientListAlgebra.polynomial (interpret n x::xs.map (interpret n))=0
      rw [ih,hs,polynomial_cons_zero_iff]
      rfl

end PlanarHom.DensePolynomial
