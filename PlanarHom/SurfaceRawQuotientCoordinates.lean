import PlanarHom.SurfaceRawCycleRows
import PlanarHom.SurfaceRawFaceSpan
import PlanarHom.SurfaceQuotientCoordinates
import PlanarHom.SurfaceBooleanQuotientMachines

/-! NEW actual supplied-row homology coordinate construction. The semantic
record is proved from the computed matrices and their polynomial list program. -/
noncomputable section
namespace PlanarHom.SurfaceRawHomology
open SurfaceBooleanRows Complexity PlanarityLRRealization PairProjectionMachines

def data (g : MixedCode) (rows : PlanarityRowFaceCode.Rows) : QuotientData :=
  prepareQuotient (faceRows g rows) (cycleRows g)
def dimension (g : MixedCode) (rows : PlanarityRowFaceCode.Rows) : ℕ := (data g rows).2.length

theorem fp_data : FP PlanarityRowFaceCode.inputCode quotientDataCode (fun p => data p.1 p.2) :=
  (fp_faceRows.pair ((fp_fst MixedCode.encoding PlanarityRowFaceCode.rowsCode).comp fp_cycleRows)).comp
    fp_prepareQuotient

theorem fp_dimension : FP PlanarityRowFaceCode.inputCode BitEncoding.nat (fun p => dimension p.1 p.2) :=
  (fp_data.comp (fp_snd basisCode basisCode)).comp (ListCodecMachines.fp_length pivotCode)

variable {bt ut : ℕ} (g : MixedCode) (hg : g.Valid bt ut)
variable (rows : PlanarityRowFaceCode.Rows) (R : RotationRows (g.toMultiGraph hg))
variable (hrows : PlanarityRowFaceCode.Realizes g hg rows R)

include hg R hrows in
theorem face_inputSpan_le_cycle : inputSpan (faceRows g rows) ≤ inputSpan (cycleRows g) := by
  rw [inputSpan_eq_extend_on g.edges.length _ (fun r hr => le_of_eq (faceRows_width g rows r hr)),
    inputSpan_eq_extend_on g.edges.length _ (fun r hr => le_of_eq (cycleRows_width g r hr))]
  apply Submodule.map_mono
  rw [faceRows_span g hg rows R hrows,cycleRows_span g hg R]
  exact R.faceBoundarySpace_le

include hg R hrows in
theorem quotientLiftOn_closed (x : Fin (dimension g rows)→ZMod 2) :
    quotientLiftOn g.edges.length (faceRows g rows) (cycleRows g) x∈R.cycleSpace := by
  have hx := quotientLift_mem (faceRows g rows) (cycleRows g)
    (face_inputSpan_le_cycle g hg rows R hrows) x
  rw [inputSpan_eq_extend_on g.edges.length _ (fun r hr => le_of_eq (cycleRows_width g r hr))] at hx
  obtain ⟨y,hy,he⟩ := hx
  rw [←cycleRows_span g hg R]
  change restrictVector g.edges.length (quotientLift (faceRows g rows) (cycleRows g) x)∈_
  rw [←he,restrict_extend]
  exact hy

def computedCoordinates : R.QuotientCoordinates (dimension g rows) where
  encode := quotientEncodeOn g.edges.length (faceRows g rows) (cycleRows g)
  lift := (quotientLiftOn g.edges.length (faceRows g rows) (cycleRows g)).codRestrict R.cycleSpace
    (quotientLiftOn_closed g hg rows R hrows)
  encode_lift x := quotientEncodeOn_lift g.edges.length (faceRows g rows) (cycleRows g)
    (fun r hr => le_of_eq (cycleRows_width g r hr)) (face_inputSpan_le_cycle g hg rows R hrows) x
  kernel c := by
    change quotientEncodeOn g.edges.length (faceRows g rows) (cycleRows g) c.val=0 ↔ R.homologyClass c=0
    rw [quotientEncodeOn_kernel g.edges.length (faceRows g rows) (cycleRows g)
      (fun r hr => le_of_eq (faceRows_width g rows r hr))
      (fun r hr => le_of_eq (cycleRows_width g r hr)) c.val (by rw [cycleRows_span g hg R];exact c.property),
      faceRows_span g hg rows R hrows]
    exact (R.homologyClass_eq_zero_iff c).symm

end PlanarHom.SurfaceRawHomology
