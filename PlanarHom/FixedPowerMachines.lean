import PlanarHom.RestrictedIterationMachine
import PlanarHom.FixedFieldArithmeticMachines
import PlanarHom.FixedPowerHeights
import PlanarHom.BoundedUnaryMachines

/-! Actual polynomial-time fixed-field powers with a unary exponent, using
proved coordinate-height bounds for every intermediate multiplication. -/
namespace PlanarHom.FixedPowerMachines
open Turing PlanarHom.Complexity PlanarHom.MachineComposition
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

omit [Algebra ℚ K] in
private theorem multiply_iterate (A : K) (n : ℕ) : (fun x=>x*A)^[n] 1=A^n:=by
  induction n with
  | zero=>simp
  | succ n ih=>simp [Function.iterate_succ_apply',ih,pow_succ]

/-- `A` and its rational basis are fixed problem data. The varying exponent is
unary, so the polynomial running-time claim accounts for output growth. -/
noncomputable def computer (basis : Module.Basis (Fin dimension) ℚ K) (A : K) :
    TM2ComputableInPolyTime BitEncoding.unaryNat.toFinEncoding
      (numberFieldEncoding basis).toFinEncoding (fun n=>A^n):=by
  let e:=numberFieldEncoding basis
  have bodyFP : FP e e (fun x=>x*A):=
    ((fp_id e).pair (fp_const e e A)).comp (PlanarHom.FixedFieldArithmetic.fp_multiplication basis)
  let body:=Classical.choice bodyFP
  let hpoly:=PlanarHom.FixedPowerHeights.exists_polynomial_power_length_bound basis A
  let p:=Classical.choose hpoly
  have hp:=Classical.choose_spec hpoly
  let c:=PlanarHom.BoundedIterationMachine.fromSeedComputer e (fun x=>x*A) 1 body p
    (fun n i hi=>by simpa only [multiply_iterate] using hp n i hi)
  have he : (fun n=>(fun x : K=>x*A)^[n] 1)=(fun n=>A^n):=funext (multiply_iterate A)
  rw [he] at c
  exact c

theorem fp_power (basis : Module.Basis (Fin dimension) ℚ K) (A : K) :
    FP BitEncoding.unaryNat (numberFieldEncoding basis) (fun n=>A^n):=⟨computer basis A⟩

/-- Binary exponents are expanded only under an explicit unary cap. In the
exponent-vector application the proved coordinate bound makes the cap exact. -/
noncomputable def boundedComputer (basis : Module.Basis (Fin dimension) ℚ K) (A : K) :
    TM2ComputableInPolyTime (BitEncoding.unaryNat.prod BitEncoding.nat).toFinEncoding
      (numberFieldEncoding basis).toFinEncoding (fun p=>A^(min p.1 p.2)):=
  composeComputers PlanarHom.BoundedUnaryMachines.computer (computer basis A)

end PlanarHom.FixedPowerMachines
