import PlanarHom.DenseGridInterpolation

/-! NEW actual fixed-dimensional grid sampling. Every grid point and every
rational call is materialized by nested FP list maps; dimension alone is fixed. -/
noncomputable section
namespace PlanarHom.DensePolynomial
open Complexity PairProjectionMachines

 theorem evalHom_cons (n:ℕ) (x:ℚ) (point:List ℚ) (P:Poly (n+1)) :
    evalHom (n+1) (x::point) P=evalHom n point (P.eval (qHom n x)) := by
  change Polynomial.eval₂ (evalHom n point) x P=_
  rw [Polynomial.eval,Polynomial.hom_eval₂,evalHom_qHom]
  rfl

 def tabulate : (n:ℕ)→ℕ→(List ℚ→ℚ)→List ℚ→Code n
  | 0,_,f,pre=>f pre
  | n+1,d,f,pre=>(List.range (d+1)).map
      (fun (j:ℕ)=>tabulate n d f (pre++[(j:ℚ)]))

 theorem tabulate_eq_samples (n d:ℕ) (f:List ℚ→ℚ) (pre:List ℚ) (P:Poly n)
    (h:∀point,point.length=n→f (pre++point)=evalHom n point P) :
    tabulate n d f pre=samples n d P := by
  induction n generalizing pre with
  | zero=>simpa [tabulate,samples,evalHom] using h [] rfl
  | succ n ih=>
    unfold tabulate samples
    have he:(List.range (d+1)).map (fun (j:ℕ)=>tabulate n d f (pre++[(j:ℚ)]))=
        List.ofFn (fun j:Fin (d+1)=>tabulate n d f (pre++[(j.val:ℚ)])) := by
      apply List.ext_getElem (by simp)
      intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rw [he]
    congr 1
    funext j
    apply ih
    intro point hp
    rw [List.append_assoc]
    simpa only [List.singleton_append] using
      (h ((j.val:ℚ)::point) (by simp [hp])).trans (evalHom_cons n _ point P)

 theorem fp_tabulate {A:Type} (e:BitEncoding A) (f:A→List ℚ→ℚ)
    (hf:FP (e.prod rationalCode.list) rationalCode (fun p=>f p.1 p.2)) (n:ℕ) :
    FP (BitEncoding.unaryNat.prod (e.prod rationalCode.list)) (encoding n)
      (fun p=>tabulate n p.1 (f p.2.1) p.2.2) := by
  induction n with
  | zero=>exact (fp_snd BitEncoding.unaryNat (e.prod rationalCode.list)).comp hf
  | succ n ih=>
    let ec:=BitEncoding.unaryNat.prod (e.prod rationalCode.list)
    have hd:=fp_fst BitEncoding.unaryNat (e.prod rationalCode.list)
    have hr:=(hd.comp UnaryArithmeticMachines.fp_succ).comp UnaryArithmeticMachines.fp_range
    have hx:=fp_fst ec BitEncoding.nat
    have hj:=(fp_snd ec BitEncoding.nat).comp (FixedFieldPolynomialMachines.fp_natCast rationalBasis)
    have hs:=(hj.pair (fp_const (ec.prod BitEncoding.nat) rationalCode.list [])).comp
      (ListMutationMachines.fp_cons rationalCode)
    have hp:=(hx.comp (fp_snd BitEncoding.unaryNat (e.prod rationalCode.list)))
    have hn:=((hp.comp (fp_snd e rationalCode.list)).pair hs).comp
      (ListMutationMachines.fp_append rationalCode)
    have hi:=((hx.comp hd).pair ((hp.comp (fp_fst e rationalCode.list)).pair hn)).comp ih
    exact (((fp_id ec).pair hr).comp
      (ListContextMachines.fp_mapWithContext ec BitEncoding.nat (encoding n) _ hi))

 def gridRecover (n d:ℕ) (f:List ℚ→ℚ) : Code n :=
    interpolate n d (tabulate n d f [])

 theorem gridRecover_eq (n d:ℕ) (f:List ℚ→ℚ) (P:Poly n) (hP:BoxDegree n d P)
    (hf:∀point,point.length=n→f point=evalHom n point P) :
    interpret n (gridRecover n d f)=P := by
  rw [gridRecover,tabulate_eq_samples n d f [] P (by simpa using hf)]
  exact interpolate_samples n d P hP

 theorem fp_gridRecover {A:Type} (e:BitEncoding A) (f:A→List ℚ→ℚ)
    (hf:FP (e.prod rationalCode.list) rationalCode (fun p=>f p.1 p.2)) (n:ℕ) :
    FP (BitEncoding.unaryNat.prod e) (encoding n) (fun p=>gridRecover n p.1 (f p.2)) := by
  have hd:=fp_fst BitEncoding.unaryNat e
  have ha:=fp_snd BitEncoding.unaryNat e
  have hi:=hd.pair (ha.pair (fp_const (BitEncoding.unaryNat.prod e) rationalCode.list []))
  exact (hd.pair (hi.comp (fp_tabulate e f hf n))).comp (fp_interpolate n)

end PlanarHom.DensePolynomial
