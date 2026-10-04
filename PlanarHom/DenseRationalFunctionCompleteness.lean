import PlanarHom.DenseRationalFunctionSemantics

/-! Every actual rational function has a valid dense fraction representative.
This is representation completeness, not a canonical normalization algorithm. -/
noncomputable section
open Classical
namespace PlanarHom.DensePolynomial

theorem interpret_surjective (n:ℕ) : Function.Surjective (interpret n) := by
  induction n with
  | zero => exact fun p=>⟨p,rfl⟩
  | succ n ih =>
    intro p
    let c:Poly n→Code n:=fun a=>Classical.choose (ih a)
    have hc:∀a,interpret n (c a)=a:=fun a=>Classical.choose_spec (ih a)
    let xs:Code (n+1):=List.ofFn (fun i:Fin (p.natDegree+1)=>c (p.coeff i.val))
    refine ⟨xs,?_⟩
    apply Polynomial.ext
    intro k
    rw [interpret_coeff]
    by_cases hk:k<p.natDegree+1
    · have hg:xs[k]?=some (c (p.coeff k)) := by
        change (List.ofFn (fun i:Fin (p.natDegree+1)=>c (p.coeff i.val)))[k]?=_
        simp only [List.getElem?_ofFn,hk,↓reduceDIte]
      rw [hg,Option.getD_some,hc]
    · have hg:xs[k]?=none := by
        apply List.getElem?_eq_none
        simp only [xs,List.length_ofFn]
        omega
      rw [hg,Option.getD_none,interpret_zero]
      symm
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem fraction_complete (n:ℕ) (x:RationalFunction n) :
    ∃a:FractionCode n,FractionValid n a ∧ fractionValue n a=x := by
  obtain ⟨p,q,hq,h⟩:=IsFractionRing.div_surjective (A:=Poly n) x
  obtain ⟨pc,hp⟩:=interpret_surjective n p
  obtain ⟨qc,hqc⟩:=interpret_surjective n q
  refine ⟨(pc,qc),?_,?_⟩
  · change interpret n qc≠0
    rw [hqc]
    exact mem_nonZeroDivisors_iff_ne_zero.mp hq
  · simpa only [fractionValue,hp,hqc] using h

end PlanarHom.DensePolynomial
