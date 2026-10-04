import PlanarHom.RestrictedIterationMachine
import PlanarHom.GraphParallelCode

/-! Actual unary-to-canonical-binary conversion by bounded successor iteration. -/
namespace PlanarHom.UnaryNatConversionMachine
open Turing Polynomial PlanarHom.Complexity PlanarHom.BinaryArithmetic

private theorem successor_iterate (n : ℕ) : (fun x : ℕ=>x+1)^[n] 0=n:=by
  induction n with
  | zero=>rfl
  | succ n ih=>simp [Function.iterate_succ_apply',ih]

noncomputable def computer :
    TM2ComputableInPolyTime BitEncoding.unaryNat.toFinEncoding BitEncoding.nat.toFinEncoding id:=by
  let c:=PlanarHom.BoundedIterationMachine.fromSeedComputer BitEncoding.nat (fun x=>x+1) 0
    successorComputable X (fun n i hi=>by
      simpa only [successor_iterate,Polynomial.eval_X] using (encodeNat_length_le i).trans hi)
  have he : (fun n=>(fun x : ℕ=>x+1)^[n] 0)=id:=funext successor_iterate
  rw [he] at c
  exact c

theorem fp_conversion : FP BitEncoding.unaryNat BitEncoding.nat id:=⟨computer⟩

end PlanarHom.UnaryNatConversionMachine
