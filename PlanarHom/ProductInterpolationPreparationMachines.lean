import PlanarHom.LagrangeRecoveryMachines
import PlanarHom.RepresentativeWordCertificates
import PlanarHom.GraphInterpolationQueries

/-! # Actual context preparation and recovery rebracketing for product interpolation -/
namespace PlanarHom.ProductInterpolationPreparationMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open LagrangeCoefficientMachines
variable {K I : Type} [Field K]

/-- Exactly the metadata retained by one framed nonadaptive query context. -/
def Ctx (A : I→K) := {p : ℕ×List (K×K) // NodesValid A p.1 (p.2.map Prod.fst)}

variable [DecidableEq K] [Algebra ℚ K] [Fintype I] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K) (A : I→K)

noncomputable def metadataEncoding : BitEncoding (Ctx A) :=
  (BitEncoding.unaryNat.prod ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list).restrict
    (fun p => NodesValid A p.1 (p.2.map Prod.fst))

def recoveryInput (p : Ctx A×List K) : LagrangeRecoveryMachines.Input A :=
  ⟨(p.1.val.1,(p.1.val.2,p.2)),p.1.property⟩

def recoverContext (p : Ctx A×List K) : K := LagrangeRecoveryMachines.recover A (recoveryInput A p)

/-- Move from ((m,table),answers) to (m,(table,answers)) with actual projections
and pairing. The input's single metadata frame is not reinterpreted for free. -/
theorem fp_recover_context : FP ((metadataEncoding basis A).prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis) (recoverContext A) := by
  have hc := fp_fst (metadataEncoding basis A) (numberFieldEncoding basis).list
  have hy := fp_snd (metadataEncoding basis A) (numberFieldEncoding basis).list
  have hv : FP (metadataEncoding basis A)
      (BitEncoding.unaryNat.prod ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list)
      (fun c => c.val) := fp_code_view _ _ _ (fun _ => rfl)
  have hm := (hc.comp hv).comp (fp_fst BitEncoding.unaryNat _)
  have ht := (hc.comp hv).comp (fp_snd BitEncoding.unaryNat _)
  have hp : FP ((metadataEncoding basis A).prod (numberFieldEncoding basis).list)
      (LagrangeRecoveryMachines.inputEncoding basis A) (recoveryInput A) :=
    (hm.pair (ht.pair hy)).transportOutput (fun _ => rfl)
  exact hp.comp (LagrangeRecoveryMachines.fp_recover basis A)

variable {t : ℕ}

/-- Actual retained rows carry the source-word certificate proved from their
original exponent-vector representatives. No target reconstruction is used. -/
def metadataFor (A B : Fin t→K) (m : ℕ) : Ctx A :=
  ⟨(m,ExponentProductTables.representatives A B m),ExponentProductTables.source_nodes_valid A B m⟩

theorem fp_metadataFor (A B : Fin t→K) : FP BitEncoding.unaryNat (metadataEncoding basis A)
    (metadataFor A B) := by
  exact ((fp_id BitEncoding.unaryNat).pair (ExponentProductTables.fp_representatives basis A B)).transportOutput
    (fun _ => rfl)

def binaryPreparation (A B : Fin t→K) (selected : ℕ) (g : MixedCode) : Ctx A×List MixedCode :=
  (metadataFor A B (g.markedCount selected),GraphInterpolationQueries.queries (MixedCode.parallelLabel selected)
    ((ExponentProductTables.representatives A B (g.markedCount selected)).length,g))

def unaryPreparation (A B : Fin t→K) (selected : ℕ) (g : MixedCode) : Ctx A×List MixedCode :=
  (metadataFor A B (g.unaryMarkedCount selected),GraphInterpolationQueries.queries (MixedCode.parallelUnaryLabel selected)
    ((ExponentProductTables.representatives A B (g.unaryMarkedCount selected)).length,g))

/-- Compute the real selected binary occurrence count, certified representative
table, and ascending positive thickening-query batch from a typed mixed code. -/
theorem fp_binaryPreparation (A B : Fin t→K) (selected : ℕ) :
    FP MixedCode.encoding ((metadataEncoding basis A).prod MixedCode.encoding.list)
      (binaryPreparation A B selected) :=
  ((MixedCode.fp_unaryMarkedCount selected).comp (fp_metadataFor basis A B)).pair
    (GraphInterpolationQueries.fp_binaryBatch basis A B selected)

/-- Unary-label counterpart, retaining every original binary and other unary
occurrence through the already proved actual query transformations. -/
theorem fp_unaryPreparation (A B : Fin t→K) (selected : ℕ) :
    FP MixedCode.encoding ((metadataEncoding basis A).prod MixedCode.encoding.list)
      (unaryPreparation A B selected) :=
  ((MixedCode.fp_unaryMarkedCount_unary selected).comp (fp_metadataFor basis A B)).pair
    (GraphInterpolationQueries.fp_unaryBatch basis A B selected)

end PlanarHom.ProductInterpolationPreparationMachines
