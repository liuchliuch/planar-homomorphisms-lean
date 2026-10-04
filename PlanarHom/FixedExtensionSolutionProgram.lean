import PlanarHom.FixedExtensionSystemProgram
import PlanarHom.DenseRationalSystemCorrectness
import PlanarHom.BinaryMultiplicationMachine

/-! The extension solution is reconstructed from consecutive fixed-size blocks
of rational-function solutions, using proved common-denominator clearing. -/
noncomputable section
namespace PlanarHom.FixedRealExtension
open DensePolynomial Complexity PairProjectionMachines

def solutionCoordinate (n e:ℕ) (xs:List (FractionCode n)) (i:ℕ) (k:Fin e) : FractionCode n :=
  xs[k.val+e*i]?.getD (fractionZero n)

def restore (n e:ℕ) (N:ℕ) (xs:List (FractionCode n)) : List (Code n e) :=
  (List.range N).map (fun i=>packFractions n e (solutionCoordinate n e xs i))

def solve {n e:ℕ} (T:MultiplicationTable n e) (p:System n e) : List (Code n e) :=
  restore n e p.1.length (DensePolynomial.solve n (expand T p))

theorem fp_solutionCoordinate (n e:ℕ) (k:Fin e) :
    FP ((fractionEncoding n).list.prod BitEncoding.nat) (fractionEncoding n)
      (fun p=>solutionCoordinate n e p.1 p.2 k) := by
  let ei:=(fractionEncoding n).list.prod BitEncoding.nat
  have hi:=fp_snd (fractionEncoding n).list BitEncoding.nat
  have hm:=((fp_const ei BitEncoding.nat e).pair hi).comp BinaryArithmetic.fp_multiplication
  have hj:=((fp_const ei BitEncoding.nat k.val).pair hm).comp BinaryArithmetic.fp_addition
  exact (hj.pair (fp_fst (fractionEncoding n).list BitEncoding.nat)).comp (fp_codeLookup (fractionEncoding n) (fractionZero n))

theorem fp_restore (n e:ℕ) :
    FP (BitEncoding.unaryNat.prod (fractionEncoding n).list) (encoding n e).list
      (fun p=>restore n e p.1 p.2) := by
  let ef:=(fractionEncoding n).list
  have hv:FP (ef.prod BitEncoding.nat) ((fractionEncoding n).vector e)
      (fun p=>solutionCoordinate n e p.1 p.2) :=
    FixedVectorMachines.fp_assemble _ _ _ _ (fp_solutionCoordinate n e)
  have hb:=hv.comp (fp_packFractions n e)
  have hxs:=fp_snd BitEncoding.unaryNat ef
  have hr:=(fp_fst BitEncoding.unaryNat ef).comp UnaryArithmeticMachines.fp_range
  exact (hxs.pair hr).comp (ListContextMachines.fp_mapWithContext ef BitEncoding.nat (encoding n e) _ hb)

theorem fp_solve {n e:ℕ} (T:MultiplicationTable n e) :
    FP (systemEncoding n e) (encoding n e).list (solve T) :=
  ((fp_systemOrder n e).pair ((fp_expand T).comp (DensePolynomial.fp_solve n))).comp (fp_restore n e)

@[simp] theorem solve_length {n e:ℕ} (T:MultiplicationTable n e) (p:System n e) :
    (solve T p).length=p.1.length := by simp [solve,restore]

end PlanarHom.FixedRealExtension
