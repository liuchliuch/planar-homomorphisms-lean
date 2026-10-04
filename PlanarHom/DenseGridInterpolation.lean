import PlanarHom.DenseGridWeights
import PlanarHom.DensePolynomialBoxDegree

/-! NEW fixed-variable interpolation on a materialized integer grid tensor.
No polynomial-field arithmetic or coefficient oracle is used by the program. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.DensePolynomial
open Complexity PairProjectionMachines

def interpolateColumn (n d k:ℕ) (xs:List (Code n)) : Code n :=
  sum n (xs.zipIdx.map (fun p=>scalar n (gridWeight d k p.2) p.1))

def interpolate : (n:ℕ)→ℕ→Code n→Code n
  | 0,_,x=>x
  | n+1,d,xs=>(List.range (d+1)).map
      (fun k=>interpolateColumn n d k (xs.map (interpolate n d)))

 theorem interpolateColumn_ofFn (n d:ℕ) (xs:Fin (d+1)→Code n) (k:ℕ) :
    interpret n (interpolateColumn n d k (List.ofFn xs))=
      ∑j:Fin (d+1),qHom n (gridWeight d k j.val)*interpret n (xs j) := by
  rw [interpolateColumn,interpret_sum]
  simp only [List.map_map,Function.comp_def,interpret_scalar]
  have he:(List.ofFn xs).zipIdx=List.ofFn (fun j:Fin (d+1)=>(xs j,j.val)) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp only [List.getElem_zipIdx,List.getElem_ofFn,Nat.zero_add]
  rw [he,List.map_ofFn,List.sum_ofFn]
  rfl

 theorem interpolate_step (n d:ℕ) (P:Polynomial (Poly n)) (hP:P.natDegree≤d)
    (xs:Fin (d+1)→Code n)
    (hxs:∀j,interpret n (interpolate n d (xs j))=P.eval (qHom n (j.val:ℚ))) :
    interpret (n+1) (interpolate (n+1) d (List.ofFn xs))=P := by
  apply Polynomial.ext
  intro k
  rw [interpret_coeff]
  by_cases hk:k<d+1
  · have hget:(interpolate (n+1) d (List.ofFn xs))[k]?=
        some (interpolateColumn n d k ((List.ofFn xs).map (interpolate n d))) := by
      change ((List.range (d+1)).map _)[k]?=_
      rw [List.getElem?_map,List.getElem?_range hk]
      rfl
    rw [hget,Option.getD_some,List.map_ofFn,interpolateColumn_ofFn]
    simp only [Function.comp_def,hxs]
    exact grid_coefficient n d P hP ⟨k,hk⟩
  · have hget:(interpolate (n+1) d (List.ofFn xs))[k]?=none := by
      apply List.getElem?_eq_none
      simp only [interpolate,List.length_map,List.length_range]
      omega
    rw [hget,Option.getD_none,interpret_zero]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP (by omega))).symm

/-- Exact full tensor of rational samples of an original polynomial. -/
def samples : (n:ℕ)→ℕ→Poly n→Code n
  | 0,_,P=>P
  | n+1,d,P=>List.ofFn (fun j:Fin (d+1)=>samples n d (P.eval (qHom n (j.val:ℚ))))

 theorem interpolate_samples (n d:ℕ) (P:Poly n) (hP:BoxDegree n d P) :
    interpret n (interpolate n d (samples n d P))=P := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    apply interpolate_step n d P hP.1
    intro j
    exact ih _ (boxDegree_eval n d P hP.2 (j.val:ℚ))

 theorem fp_interpolateColumn (n:ℕ) :
    FP ((BitEncoding.unaryNat.prod BitEncoding.nat).prod (encoding n).list) (encoding n)
      (fun p=>interpolateColumn n p.1.1 p.1.2 p.2) := by
  let ec:=BitEncoding.unaryNat.prod BitEncoding.nat
  let e:=encoding n
  have hx:=fp_snd ec e.list
  have hc:=fp_fst ec e.list
  have hp:=fp_snd ec (e.prod BitEncoding.nat)
  have hw:=((fp_fst ec (e.prod BitEncoding.nat)).pair
    (hp.comp (fp_snd e BitEncoding.nat))).comp fp_gridWeight
  have hs:=(hw.pair (hp.comp (fp_fst e BitEncoding.nat))).comp (fp_scalar n)
  exact (((hc.pair (hx.comp (ListIndexMachines.fp_zipIdx e))).comp
    (ListContextMachines.fp_mapWithContext ec (e.prod BitEncoding.nat) e _ hs)).comp (fp_sum n))

 theorem fp_interpolate (n:ℕ) : FP (BitEncoding.unaryNat.prod (encoding n)) (encoding n)
    (fun p=>interpolate n p.1 p.2) := by
  induction n with
  | zero=>exact fp_snd BitEncoding.unaryNat (encoding 0)
  | succ n ih=>
    let e:=encoding n
    let ei:=BitEncoding.unaryNat.prod e.list
    have hd:=fp_fst BitEncoding.unaryNat e.list
    have hx:=(fp_id ei).comp
      (ListContextMachines.fp_mapWithContext BitEncoding.unaryNat e e _ ih)
    have hr:=(hd.comp UnaryArithmeticMachines.fp_succ).comp UnaryArithmeticMachines.fp_range
    have hi:=fp_fst ei BitEncoding.nat
    have hk:=fp_snd ei BitEncoding.nat
    have hh:=(((hi.comp hd).pair hk).pair (hi.comp hx)).comp (fp_interpolateColumn n)
    exact (((fp_id ei).pair hr).comp
      (ListContextMachines.fp_mapWithContext ei BitEncoding.nat e _ hh))

end PlanarHom.DensePolynomial
