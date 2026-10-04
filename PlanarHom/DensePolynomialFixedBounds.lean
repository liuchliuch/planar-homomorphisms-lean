import PlanarHom.DensePolynomialSizeCertificates
import PlanarHom.DensePolynomialSemantics
import PlanarHom.EncodingSizeBounds

/-! Fixed finite polynomial families have a common rational coefficient
certificate. Exponential numerator/denominator bounds translate into actual
polynomial bit-size bounds for the complete nested dense encoding. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.DensePolynomial
open Complexity

def volume : (n:ℕ)→Code n→ℕ
  | 0,_ => 0
  | n+1,a => a.length+(a.map (volume n)).sum

def leaves : (n:ℕ)→Code n→List ℚ
  | 0,a => [a]
  | n+1,a => a.flatMap (leaves n)

theorem box_volume (n:ℕ) (a:Code n) : BoxBound n (volume n a) a := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨Nat.le_add_right _ _,?_⟩
    intro b hb
    have h:(volume n b)≤(a.map (volume n)).sum:=
      List.single_le_sum (fun x _=>Nat.zero_le x) _ (List.mem_map.mpr ⟨b,hb,rfl⟩)
    exact box_mono n (h.trans (Nat.le_add_left _ _)) (ih b)

theorem coeff_iff_leaves (n D H:ℕ) (a:Code n) :
    CoeffBound n D H a ↔ ∀q∈leaves n a,∃z:ℤ,(D:ℚ)*q=z ∧ z.natAbs≤H := by
  induction n with
  | zero => simp only [CoeffBound,leaves,List.mem_singleton,forall_eq]
  | succ n ih =>
    constructor
    · intro h q hq
      obtain ⟨b,hb,hq⟩:=List.mem_flatMap.mp hq
      exact (ih b).mp (h b hb) q hq
    · intro h b hb
      apply (ih b).mpr
      intro q hq
      exact h q (List.mem_flatMap.mpr ⟨b,hb,hq⟩)

/-- Existence here only fixes finitely many source-dependent constants. It is
not a dynamic presentation-discovery or numerical real-approximation routine. -/
theorem fixed_family_bounds {I:Type} [Fintype I] (n:ℕ) (c:I→Code n) :
    ∃W D H:ℕ,0<W ∧ 0<D ∧ 0<H ∧ ∀i,BoxBound n W (c i) ∧ CoeffBound n D H (c i) := by
  let W:=1+∑i,volume n (c i)
  let qs:=Finset.univ.toList.flatMap (fun i=>leaves n (c i))
  obtain ⟨D,hD,z,hz⟩:=IntegerCoordinateBounds.exists_common_denominator (fun j:Fin qs.length=>qs.get j)
  let H:=1+∑j,(z j).natAbs
  refine ⟨W,D,H,by dsimp[W];omega,hD,by dsimp[H];omega,?_⟩
  intro i
  constructor
  · apply box_mono n _ (box_volume n (c i))
    have hv : volume n (c i) ≤ ∑j,volume n (c j) :=
      Finset.single_le_sum (f:=fun j=>volume n (c j)) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    dsimp [W]
    omega
  · apply (coeff_iff_leaves n D H (c i)).mpr
    intro q hq
    have hmem:q∈qs:=List.mem_flatMap.mpr ⟨i,by simp,hq⟩
    obtain ⟨j,hj,hget⟩:=List.mem_iff_getElem.mp hmem
    refine ⟨z ⟨j,hj⟩,?_,?_⟩
    · simpa only [List.get_eq_getElem,hget] using hz ⟨j,hj⟩
    · have hv : (z ⟨j,hj⟩).natAbs ≤ ∑k,(z k).natAbs :=
        Finset.single_le_sum (f:=fun k=>(z k).natAbs) (fun _ _=>Nat.zero_le _)
          (Finset.mem_univ (⟨j,hj⟩ : Fin qs.length))
      dsimp [H]
      omega

def sizePolynomial : (n:ℕ)→Polynomial ℕ→ℕ→ℕ→Polynomial ℕ
  | 0,_,C,D => EncodingSizeBounds.coordinateOutputPolynomial 1 C D
  | n+1,W,C,D => (Polynomial.C 2*sizePolynomial n W C D+Polynomial.C 3)*W+1

private theorem rational_code_bound (C D L:ℕ) (hD:0<D) (a:ℚ)
    (h:CoeffBound 0 (D^L) (C^L) a) :
    ((encoding 0).encode a).length≤(EncodingSizeBounds.coordinateOutputPolynomial 1 C D).eval L := by
  obtain ⟨z,hz,hb⟩:=h
  change ((rationalCoordinates 1).encode (rationalBasis.equivFun a)).length≤_
  apply EncodingSizeBounds.rational_coordinates_length_le
  intro i
  have he:rationalBasis.equivFun a i=a := by fin_cases i; simp [rationalBasis,Module.Basis.equivFun_apply]
  refine ⟨z,D^L,?_,hb,le_rfl⟩
  rw [he,Rat.mkRat_eq_div]
  apply (eq_div_iff (by exact_mod_cast (pow_pos hD L).ne')).mpr
  simpa only [mul_comm] using hz

theorem encoded_size_bound (n:ℕ) (W:Polynomial ℕ) (C D L:ℕ) (hD:0<D) (a:Code n)
    (hbox:BoxBound n (W.eval L) a) (hc:CoeffBound n (D^L) (C^L) a) :
    ((encoding n).encode a).length≤(sizePolynomial n W C D).eval L := by
  induction n with
  | zero => exact rational_code_bound C D L hD a hc
  | succ n ih =>
    have hlen:=CoefficientListHeights.list_encoding_length_le (encoding n) a
      ((sizePolynomial n W C D).eval L) (fun b hb=>ih b (hbox.2 b hb) (hc b hb))
    have hm:=Nat.mul_le_mul_left (2*(sizePolynomial n W C D).eval L+3) hbox.1
    have hh:=hlen.trans (Nat.add_le_add_right hm 1)
    simpa only [sizePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_one] using hh

end PlanarHom.DensePolynomial
