import PlanarHom.ListMapMachines
import PlanarHom.OracleRunExtensionality

/-! A genuine oracle machine querying every encoded list item, with complete
query/answer charging and an output-size-only cost bound. -/
namespace PlanarHom.ListMapMachines
open Turing Polynomial PlanarHom.Complexity PlanarHom.MachineComposition

/-- This requires only an answer-length bound, not an algorithm for the oracle. -/
theorem mapTime_bound_of_output_bound {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β)
    (f : α→β) (p : Polynomial ℕ) (bound : ∀a,(eb.encode (f a)).length≤p.eval (ea.encode a).length)
    (xs : List α) : mapTime ea eb f xs≤((C 4*X+C 4)*(X+p+C 4)).eval (ea.list.encode xs).length:=by
  let N := (ea.list.encode xs).length
  let P := p.eval N
  let I := (xs.map (fun a => (ea.encode a).length)).sum
  have hN : N=2*(BitEncoding.nat.encode xs.length).length+1+2*I+xs.length := by
    simp [N,I,BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
    omega
  have hn : xs.length≤N := by omega
  have hi : I≤N := by omega
  have hinput (a : α) (ha : a∈xs) : (ea.encode a).length≤N :=
    (mem_le_sum_map (fun a => (ea.encode a).length) ha).trans hi
  have hout (a : α) (ha : a∈xs) : (eb.encode (f a)).length≤P :=
    (bound a).trans (natPolynomial_monotone _ (hinput a ha))
  have hcost : mapCost ea eb f xs≤N*(3*N+2*P+5) := by
    apply (sum_map_le_mul (itemCost ea eb f) xs (3*N+2*P+5) (fun a ha => ?_)).trans
      (Nat.mul_le_mul_right _ hn)
    have hia := hinput a ha
    have hoa := hout a ha
    dsimp [itemCost]
    omega
  have hsum : (xs.map (fun a => (eb.encode (f a)).length)).sum≤N*P :=
    (sum_map_le_mul (fun a => (eb.encode (f a)).length) xs P hout).trans (Nat.mul_le_mul_right P hn)
  have houtput : (eb.list.encode (xs.map f)).length ≤ N+2*N*P := by
    simp only [BitEncoding.list,List.length_append,BitEncoding.frame_length,List.length_map,
      BitEncoding.frames_length,List.map_map,Function.comp_def]
    nlinarith
  simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X]
  change mapTime ea eb f xs≤(4*N+4)*(N+P+4)
  dsimp [mapTime]
  nlinarith

end PlanarHom.ListMapMachines

namespace PlanarHom.Complexity
attribute [local instance] Classical.propDecidable

/-- Raw words satisfying any promise remain distinct representation values.
This is a semantic encoding; no machine deciding the promise is asserted. -/
noncomputable def promiseWordEncoding (valid : Bits→Prop) : BitEncoding {q : Bits // valid q} where
  encode:=Subtype.val
  decode q:=if h:valid q then some ⟨q,h⟩ else none
  decode_encode q:=by simp [q.property]

/-- An internal batch query input is a canonical list of individually valid raw
queries. Individual queries need not be canonical in the source's graph codec. -/
def batchProblem (P : PromiseProblem) : PromiseProblem where
  valid input:=∃qs : List Bits,input=BitEncoding.bits.list.encode qs ∧ ∀q∈qs,P.valid q
  value:=encodedFunction BitEncoding.bits.list BitEncoding.bits.list (List.map P.value) []

private def promisedList (P : PromiseProblem) (qs : List Bits) (h : ∀q∈qs,P.valid q) :
    List {q : Bits // P.valid q}:=qs.attach.map (fun q=>⟨q.val,h q.val q.property⟩)

private theorem promisedList_values (P : PromiseProblem) (qs : List Bits) (h : ∀q∈qs,P.valid q) :
    (promisedList P qs h).map Subtype.val=qs:=by
  rw [promisedList,List.map_map]
  exact List.attach_map_subtype_val qs

/-- Actual repeated queries against every valid extension of the source oracle.
The only source hypothesis is the already-proved polynomial answer bit bound. -/
noncomputable def batchReduction (P : PromiseProblem) (p : Polynomial ℕ)
    (bound : ∀q,P.valid q→(P.value q).length≤p.eval q.length) :
    PromisePolyTimeTuringReduction (batchProblem P) P where
  machine:=PlanarHom.ListMapMachines.machine
  time:=(Polynomial.C 4*Polynomial.X+Polynomial.C 4)*(Polynomial.X+p+Polynomial.C 4)
  computes oracle ho input hi:=by
    obtain ⟨qs,rfl,hvalid⟩:=hi
    let e:=promiseWordEncoding P.valid
    let items:=promisedList P qs hvalid
    let f : {q : Bits // P.valid q}→Bits:=fun q=>P.value q.val
    have hv : items.map Subtype.val=qs:=promisedList_values P qs hvalid
    have henc : e.list.encode items=BitEncoding.bits.list.encode qs:=by
      have hl : items.length=qs.length:=by simpa only [List.length_map] using congrArg List.length hv
      simp only [BitEncoding.list,e,promiseWordEncoding,BitEncoding.bits,hl,hv,List.map_id]
    have hout : items.map f=qs.map P.value:=by
      rw [←hv,List.map_map]
      rfl
    obtain ⟨steps,cost,trace,hr,hcost,hgood⟩:=PlanarHom.ListMapMachines.run (ea:=e) (eb:=BitEncoding.bits) (f:=f) items
    have htime:=PlanarHom.ListMapMachines.mapTime_bound_of_output_bound e BitEncoding.bits f p
      (fun q=>bound q.val q.property) items
    have hrun:=hr.changeOracle (replacement:=oracle) (fun q a hqa=>by
      obtain ⟨x,hx⟩:=hgood (q,a) hqa
      cases hx
      exact ho x.val x.property)
    refine ⟨steps,cost,trace,?_,?_,?_⟩
    · rw [henc,hout] at hrun
      simpa only [batchProblem,encodedFunction_encode] using hrun
    · rw [henc] at htime
      exact hcost.trans htime
    · intro q a hqa
      obtain ⟨x,hx⟩:=hgood (q,a) hqa
      have hq:=congrArg Prod.fst hx
      dsimp only [e,promiseWordEncoding] at hq
      simpa only [hq] using x.property

end PlanarHom.Complexity
