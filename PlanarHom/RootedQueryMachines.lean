import PlanarHom.RootedCodeNormalization
import PlanarHom.FieldDotProductMachines
import PlanarHom.LagrangeRecoveryListSemantics

/-! Actual fixed rooted-query batch and original-field coefficient dot product. -/
noncomputable section
namespace PlanarHom.RootedRestriction
open Complexity PairProjectionMachines FixedVectorMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension k : ℕ}

def prepare (graphs : Fin k → FiniteRootedPlanar) (p : ℕ × MixedCode) : ℕ × List MixedCode :=
  (0,List.ofFn (fun j => RootedCodeMachines.attach (graphs j).2.2.val 0 p))

def recover (c : Fin k → K) (p : ℕ × List K) : K :=
  (List.zipWith (· * ·) (List.ofFn c) p.2).sum

theorem fp_prepare (graphs : Fin k → FiniteRootedPlanar) :
    FP RootedCodeMachines.inputEncoding (BitEncoding.nat.prod MixedCode.encoding.list) (prepare graphs) := by
  have h := fp_assemble RootedCodeMachines.inputEncoding MixedCode.encoding k
    (fun p j => RootedCodeMachines.attach (graphs j).2.2.val 0 p)
    (fun j => RootedCodeMachines.fp_attach (graphs j).2.2.val 0)
  have hlist : FP RootedCodeMachines.inputEncoding MixedCode.encoding.list
      (fun p => List.ofFn (fun j => RootedCodeMachines.attach (graphs j).2.2.val 0 p)) :=
    h.transportOutput (fun _ => rfl)
  exact (fp_const _ BitEncoding.nat 0).pair hlist

theorem fp_recover (basis : Module.Basis (Fin dimension) ℚ K) (c : Fin k → K) :
    FP (BitEncoding.nat.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) (recover c) :=
  ((fp_const _ (numberFieldEncoding basis).list (List.ofFn c)).pair
    (fp_snd BitEncoding.nat (numberFieldEncoding basis).list)).comp (FieldDotProductMachines.fp_dot basis)

omit [Algebra ℚ K] in
theorem recover_ofFn (c y : Fin k → K) (tag : ℕ) :
    recover c (tag,List.ofFn y) = ∑ j, c j * y j := by
  simp [recover,LagrangeRecoveryListSemantics.zipWith_ofFn,List.sum_ofFn]

end PlanarHom.RootedRestriction
