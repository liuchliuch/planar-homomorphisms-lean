import PlanarHom.BoundedIterationMachine
import PlanarHom.ListMutationMachines
import PlanarHom.GraphParallelCode

/-! Polynomial-time explicit range enumeration from a unary size parameter. -/
namespace PlanarHom.UnaryRangeMachines
open Turing Polynomial PlanarHom.Complexity PlanarHom.MachineComposition PlanarHom.MachinePairing

def prependLength (xs : List ℕ) : List ℕ:=xs.length::xs

theorem fp_prependLength : FP BitEncoding.nat.list BitEncoding.nat.list prependLength:=
  ((ListCodecMachines.fp_length BitEncoding.nat).pair (fp_id BitEncoding.nat.list)).comp
    (PlanarHom.ListMutationMachines.fp_cons BitEncoding.nat)

private def weight (xs : List ℕ) : ℕ:=(xs.map (fun a=>(BitEncoding.nat.encode a).length)).sum

private theorem list_length (xs : List ℕ) :
    (BitEncoding.nat.list.encode xs).length=
      2*(BitEncoding.nat.encode xs.length).length+1+2*weight xs+xs.length:=by
  simp only [BitEncoding.list,List.length_append,BitEncoding.frame_length,BitEncoding.frames_length,
    List.map_map,List.length_map,Function.comp_def,weight]
  omega

private theorem iterate_length (i : ℕ) (xs : List ℕ) :
    (prependLength^[i] xs).length=xs.length+i:=by
  induction i with
  | zero=>simp
  | succ i ih=>simp [Function.iterate_succ_apply',prependLength,ih,Nat.add_assoc]

private theorem iterate_weight (i : ℕ) (xs : List ℕ) :
    weight (prependLength^[i] xs)≤weight xs+i*(xs.length+i):=by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    change (BitEncoding.nat.encode (prependLength^[i] xs).length).length+weight (prependLength^[i] xs)≤_
    have h:=encodeNat_length_le (prependLength^[i] xs).length
    rw [iterate_length] at h ⊢
    nlinarith

private theorem iterate_size_bound (n : ℕ) (xs : List ℕ) (i : ℕ) (hi : i≤n) :
    (BitEncoding.nat.list.encode (prependLength^[i] xs)).length≤
      (C 12*(X+1)^2).eval ((BitEncoding.unaryNat.prod BitEncoding.nat.list).encode (n,xs)).length:=by
  let N:=((BitEncoding.unaryNat.prod BitEncoding.nat.list).encode (n,xs)).length
  have hN : N=2*n+1+(BitEncoding.nat.list.encode xs).length:=by
    simp only [N,BitEncoding.prod_length,BitEncoding.unaryNat_length]
    omega
  have hn : n≤N:=by omega
  have hx : xs.length≤N:=(BitEncoding.list_length_le BitEncoding.nat xs).trans (by omega)
  have hw : weight xs≤N:=by have h:=list_length xs; omega
  have hil : i≤N:=hi.trans hn
  have hlen : (prependLength^[i] xs).length≤2*N:=by rw [iterate_length]; omega
  have hweight : weight (prependLength^[i] xs)≤N+2*N^2:=by
    have h:=iterate_weight i xs
    have hm:=Nat.mul_le_mul hil (show xs.length+i≤2*N by omega)
    nlinarith
  have hcode:=encodeNat_length_le (prependLength^[i] xs).length
  rw [list_length]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _≤12*(N+1)^2
  nlinarith

noncomputable def enumerateFromComputer :
    TM2ComputableInPolyTime (BitEncoding.unaryNat.prod BitEncoding.nat.list).toFinEncoding
      BitEncoding.nat.list.toFinEncoding (fun p=>prependLength^[p.1] p.2):=
  PlanarHom.BoundedIterationMachine.computer BitEncoding.nat.list prependLength
    (Classical.choice fp_prependLength) (C 12*(X+1)^2) iterate_size_bound

/-- Descending enumeration `[n-1,...,0]`; the input count is explicitly unary. -/
noncomputable def rangeComputer :
    TM2ComputableInPolyTime BitEncoding.unaryNat.toFinEncoding BitEncoding.nat.list.toFinEncoding
      (fun n=>(List.range n).reverse):=by
  let c:=composeComputers
    (pairComputers (idComputableInPolyTime BitEncoding.unaryNat.toFinEncoding)
      (PlanarHom.ConstantMachines.computer BitEncoding.unaryNat BitEncoding.nat.list []))
    enumerateFromComputer
  have hr (n : ℕ) : prependLength^[n] []=(List.range n).reverse:=by
    induction n with
    | zero=>rfl
    | succ n ih=>simp [Function.iterate_succ_apply',prependLength,ih,List.range_succ]
  have he : (fun n : ℕ=>prependLength^[n] [])=(fun n=>(List.range n).reverse):=funext hr
  change TM2ComputableInPolyTime BitEncoding.unaryNat.toFinEncoding BitEncoding.nat.list.toFinEncoding
    (fun n=>prependLength^[n] []) at c
  rw [he] at c
  exact c

theorem fp_range : FP BitEncoding.unaryNat BitEncoding.nat.list (fun n=>(List.range n).reverse):=⟨rangeComputer⟩

end PlanarHom.UnaryRangeMachines
