import PlanarHom.PlanarityRowFacePrimitives
import PlanarHom.RestrictedIterationMachine

/-! NEW reconstruction. Bounded orbit materialization with a full encoded-state
polynomial, including arbitrary raw graph endpoints and arbitrary starting darts. -/
namespace PlanarHom.PlanarityRowFaceCode
open Complexity PairProjectionMachines Polynomial MachineComposition
open PlanarityRotationCode PlanarityLRDirect PlanarityLRRawConstraints

abbrev orbitInputCode := inputCode.prod dartCode
abbrev orbitStateCode := inputCode.prod (dartCode.prod dartCode.list)
abbrev OrbitState := (MixedCode×Rows)×(Dart×List Dart)
 def orbitStep (s : OrbitState) : OrbitState :=
   (s.1,(faceStep s.1.1 s.1.2 s.2.1,s.2.1::s.2.2))
 def orbitInitial (p : (MixedCode×Rows)×Dart) : OrbitState := (p.1,(p.2,[]))
 def orbitFuel (p : (MixedCode×Rows)×Dart) := 2*p.1.1.edges.length

 theorem walk_succ (g : MixedCode) (rows : Rows) (a : Dart) (n : ℕ) :
    walk g rows a (n+1)=walk g rows a n++[(faceStep g rows)^[n] a] := by
  simp [walk,List.range_succ]

 theorem orbitStep_iterate (g : MixedCode) (rows : Rows) (a : Dart) (n : ℕ) :
    orbitStep^[n] ((g,rows),(a,[])) =
      ((g,rows),((faceStep g rows)^[n] a,(walk g rows a n).reverse)) := by
  induction n with
  | zero => simp [walk]
  | succ n ih => simp [Function.iterate_succ_apply',ih,orbitStep,walk_succ]

 theorem orbit_word_bound (g : MixedCode) (rows : Rows) (a : Dart) (n : ℕ) :
    (dartCode.encode ((faceStep g rows)^[n] a)).length ≤
      2*(orbitInputCode.encode ((g,rows),a)).length+2 := by
  have hh:=iterate_word_bound g rows a n
  have hr:(rowsCode.encode rows).length≤(orbitInputCode.encode ((g,rows),a)).length:=by
    simp only [orbitInputCode,inputCode,BitEncoding.prod_length]; omega
  have ha:(dartCode.encode a).length≤(orbitInputCode.encode ((g,rows),a)).length:=by
    simp only [orbitInputCode,BitEncoding.prod_length]; omega
  exact hh.trans ((max_le hr ha).trans (by omega))

noncomputable def orbitPolynomial : Polynomial ℕ :=
  C 4*X+C 2*(C 3*(C 2*(C 2*X)*(C 2*X+C 2)+C 2*X)+1)+C 5

 theorem orbit_state_bound (p : (MixedCode×Rows)×Dart) (n : ℕ) (hn : n≤orbitFuel p) :
    (orbitStateCode.encode (orbitStep^[n] (orbitInitial p))).length ≤
      orbitPolynomial.eval (orbitInputCode.encode p).length := by
  rcases p with ⟨⟨g,rows⟩,a⟩
  let N := (orbitInputCode.encode ((g,rows),a)).length
  have hm : g.edges.length≤N := by
    have hh:=MixedCode.edges_le_length g
    simp only [N,orbitInputCode,inputCode,BitEncoding.prod_length]
    omega
  have hn' : n≤2*N := by change n≤2*g.edges.length at hn; omega
  have hw:=orbit_word_bound g rows a n
  have hl:=(PfaffianList.list_encoding_bound dartCode (walk g rows a n).reverse (2*N) (2*N+2)
    (by simp only [List.length_reverse,walk_length]; exact hn') (by
      intro b hb
      obtain ⟨i,_,rfl⟩:=List.mem_map.mp (List.mem_reverse.mp hb)
      exact orbit_word_bound g rows a i))
  have hc : (inputCode.encode (g,rows)).length≤N := by
    simp only [N,orbitInputCode,BitEncoding.prod_length]; omega
  change (orbitStateCode.encode (orbitStep^[n] ((g,rows),(a,[])))).length≤_
  rw [orbitStep_iterate]
  change (dartCode.encode ((faceStep g rows)^[n] a)).length≤2*N+2 at hw
  have hb : 2*(inputCode.encode (g,rows)).length+(2*(dartCode.encode ((faceStep g rows)^[n] a)).length+
      (dartCode.list.encode (walk g rows a n).reverse).length+1)+1 ≤
      4*N+2*(3*(2*(2*N)*(2*N+2)+2*N)+1)+5 := by omega
  simpa only [orbitStateCode,orbitPolynomial,eval_add,eval_mul,eval_C,eval_X,eval_one,
    N,orbitInputCode,inputCode,dartCode,BitEncoding.prod_length] using hb


 theorem fp_orbitStep : FP orbitStateCode orbitStateCode orbitStep := by
  have hc:=fp_fst inputCode (dartCode.prod dartCode.list)
  have ht:=fp_snd inputCode (dartCode.prod dartCode.list)
  have ha:=ht.comp (fp_fst dartCode dartCode.list)
  have hs:=ht.comp (fp_snd dartCode dartCode.list)
  have hn:=(hc.pair ha).comp fp_faceStep
  have hl:=(ha.pair hs).comp (ListMutationMachines.fp_cons dartCode)
  exact hc.pair (hn.pair hl)

 theorem fp_orbitInitial : FP orbitInputCode orbitStateCode orbitInitial :=
  (fp_fst inputCode dartCode).pair
    ((fp_snd inputCode dartCode).pair (fp_const orbitInputCode dartCode.list []))

 theorem fp_orbitFuel : FP orbitInputCode BitEncoding.unaryNat orbitFuel := by
  have hg:=(fp_fst inputCode dartCode).comp (fp_fst MixedCode.encoding rowsCode)
  have hm:=(hg.comp MixedCode.fp_edges).comp (ListUnaryLengthMachine.fp_length PlanarityDepthFirstSearch.edgeCode)
  exact ((hm.pair hm).comp UnaryArithmeticMachines.fp_add).congr (fun p=>by simp [orbitFuel,two_mul])

 def orbitPreparedCode : BitEncoding ((MixedCode×Rows)×Dart) :=
   (BitEncoding.unaryNat.prod orbitStateCode).retract
     (fun p=>(orbitFuel p,orbitInitial p)) (fun q=>(q.2.1,q.2.2.1)) (fun _=>rfl)

 theorem fp_orbit : FP orbitInputCode dartCode.list (fun p=>orbit p.1.1 p.1.2 p.2) := by
  have hprep : FP orbitInputCode orbitPreparedCode id :=
    (fp_orbitFuel.pair fp_orbitInitial).transportOutput (fun _=>rfl)
  obtain ⟨body⟩:=fp_orbitStep
  have hb (p : (MixedCode×Rows)×Dart) (n : ℕ) (hn : n≤orbitFuel p) :
      (orbitStateCode.encode (orbitStep^[n] (orbitInitial p))).length ≤
        orbitPolynomial.eval (orbitPreparedCode.encode p).length := by
    exact (orbit_state_bound p n hn).trans (natPolynomial_monotone orbitPolynomial (by
      simp only [orbitPreparedCode,BitEncoding.retract,orbitStateCode,orbitInitial,
        orbitInputCode,BitEncoding.prod_length]; omega))
  have hloop : FP orbitPreparedCode orbitStateCode (fun p=>orbitStep^[orbitFuel p] (orbitInitial p)) :=
    ⟨BoundedIterationMachine.computerOn orbitPreparedCode orbitStateCode orbitStep orbitFuel orbitInitial
      (fun _=>rfl) body orbitPolynomial hb⟩
  have hout:=(fp_snd inputCode (dartCode.prod dartCode.list)).comp (fp_snd dartCode dartCode.list)
  exact (((hprep.comp hloop).comp hout).comp (ListReverseMachines.fp_reverse dartCode)).congr (fun p=>by
    rcases p with ⟨⟨g,rows⟩,a⟩
    simp only [Function.comp_apply,id_eq,orbitInitial,orbitStep_iterate,List.reverse_reverse,orbit,orbitFuel])

end PlanarHom.PlanarityRowFaceCode
