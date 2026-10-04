import PlanarHom.SurfaceFKTListFourier
import PlanarHom.SurfaceRawCoordinateSemantics
import PlanarHom.SurfaceMatchingSupportCalibration
import PlanarHom.SurfaceGlobalPfaffianFourier

/-! NEW exact semantics of the literal support/character Pfaffian calls.
The final supplied-input wrapper discharges all row and representative facts
using the actual numeric Fisher compiler. -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceFKT
open Complexity SurfaceBooleanRows SurfaceBooleanGauss MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] [CharZero K] {kdim : ℕ}
variable (basis : Module.Basis (Fin kdim) ℚ K)

def preparedOn (cubic g : MixedCode) (rows : PlanarityRowFaceCode.Rows) (log : List ℕ) (w : List K) : Prepared K :=
  ⟨cubic,g,log,w,SurfaceRawHomology.data g rows⟩

theorem supportWeight_get (bits : Row) (i : ℕ) :
    ((bits.map (fun b => if b then (1:K) else 0)).getD i 0)=if bitAt bits i then 1 else 0 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,bitAt]
  let f : Bool→K := fun b => if b then 1 else 0
  change ((bits[i]?).map f).getD (f false)=f ((bits[i]?).getD false)
  exact Option.getD_map _ _ _

theorem twistedWeights_get_raw (p : Prepared K) (u : Row) (e : Fin p.graph.edges.length) :
    (twistedWeights p u).getD e.val 0=p.weights.getD e.val 0*
      characterValue u (encodeQuotient p.quotient (unit (SurfaceRawHomology.shape p.graph) e.val)) := by
  simp only [twistedWeights,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_zipIdx,List.getElem?_eq_getElem e.isLt,Option.map_some,Option.getD_some,Nat.zero_add]

variable (cubic g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (rows : PlanarityRowFaceCode.Rows) (R : RotationRows (g.toMultiGraph hg))
variable (hrows : PlanarityRowFaceCode.Realizes g hg rows R) (log : List ℕ) (w : List K)

include basis in
theorem calibration_eq_sign (x : Bits (SurfaceRawHomology.dimension g rows))
    (M : Finset (Fin g.edges.length)) (hM : (g.toMultiGraph hg).PerfectMatching M)
    (hmask : ∀e:Fin g.edges.length,
      bitAt (SurfaceFisherMatching.mask cubic (liftQuotient (SurfaceRawHomology.data g rows) (List.ofFn x))) e.val=
        decide (e∈M)) :
    calibration (preparedOn cubic g rows log w) (List.ofFn x)=
      (g.toMultiGraph hg).matchingPfaffianSign (R:=K) (fun e => logOrientation log e.val) M := by
  rw [calibration,OccurrenceSkewCode.evaluate_eq_pairingPfaffian basis _ hg]
  have hw : (fun e:Fin g.edges.length =>
      (supportWeights (preparedOn cubic g rows log w) (List.ofFn x)).getD e.val 0)=
      fun e => if e∈M then (1:K) else 0 := by
    funext e
    change ((SurfaceFisherMatching.mask cubic (liftQuotient (SurfaceRawHomology.data g rows) (List.ofFn x))).map
      (fun b => if b then (1:K) else 0)).getD e.val 0=_
    rw [supportWeight_get,hmask]
    simp
  change pairingPfaffian ((g.toMultiGraph hg).occurrenceSkewMatrix
    (fun e => logOrientation log e.val)
    (fun e => (supportWeights (preparedOn cubic g rows log w) (List.ofFn x)).getD e.val 0))=_
  rw [hw]
  have hh := (g.toMultiGraph hg).pairingPfaffian_matching_support (K:=K) (fun e => logOrientation log e.val) M hM
  convert hh using 1
  congr 2
  funext e
  split_ifs <;> rfl

theorem twistedWeights_get (u : Bits (SurfaceRawHomology.dimension g rows)) (e : Fin g.edges.length) :
    (twistedWeights (preparedOn cubic g rows log w) (List.ofFn u)).getD e.val 0=
      twistWeights (SurfaceRawHomology.computedCoordinates g hg rows R hrows).encode u
        (fun e:Fin g.edges.length => w.getD e.val 0) e := by
  have he := SurfaceRawHomology.encode_unit g hg rows R hrows e
  generalize hD : SurfaceRawHomology.computedCoordinates g hg rows R hrows=D at he ⊢
  have hl := twistedWeights_get_raw (preparedOn cubic g rows log w) (List.ofFn u) e
  have hc := characterValue_ofFn (K:=K) u
    (encodeQuotient (SurfaceRawHomology.data g rows) (unit (SurfaceRawHomology.shape g) e.val))
  have hh := hc.trans (congrArg (characterF2 (K:=K) u) he)
  calc
    _ = w.getD e.val 0*characterValue (List.ofFn u)
        (encodeQuotient (SurfaceRawHomology.data g rows) (unit (SurfaceRawHomology.shape g) e.val)) := hl
    _ = w.getD e.val 0*characterF2 u (D.encode (Pi.single e 1)) :=
      congrArg (fun t:K => w.getD e.val 0*t) hh
    _ = _ := by
      unfold twistWeights
      apply congrArg (fun t : K => w.getD e.val 0*t)
      apply congrArg (characterF2 (K:=K) u)
      apply congrArg D.encode
      funext f
      simp [Pi.single_apply]

theorem referenceCoordinates_value (M₀ : Finset (Fin g.edges.length))
    (hlen : (SurfaceFisherMatching.mask cubic []).length≤g.edges.length)
    (hmask : ∀e:Fin g.edges.length,bitAt (SurfaceFisherMatching.mask cubic []) e.val=decide (e∈M₀)) :
    finiteValue (SurfaceRawHomology.dimension g rows) (referenceCoordinates (preparedOn cubic g rows log w))=
      (SurfaceRawHomology.computedCoordinates g hg rows R hrows).encode (edgeIndicator M₀) := by
  change finiteValue _ (encodeQuotient (SurfaceRawHomology.data g rows) (SurfaceFisherMatching.mask cubic []))=_
  rw [SurfaceRawHomology.encode_value g hg rows R hrows _ hlen]
  congr 1
  funext e
  simp [finiteValue,SurfaceBooleanRows.value,hmask,bitValue,edgeIndicator]

include basis in
theorem twistedEvaluation_eq (M₀ : Finset (Fin g.edges.length))
    (hlen : (SurfaceFisherMatching.mask cubic []).length≤g.edges.length)
    (hmask : ∀e:Fin g.edges.length,bitAt (SurfaceFisherMatching.mask cubic []) e.val=decide (e∈M₀))
    (u : Bits (SurfaceRawHomology.dimension g rows)) :
    twistedEvaluation (preparedOn cubic g rows log w) (List.ofFn u)=
      (SurfaceRawHomology.computedCoordinates g hg rows R hrows).twistedPfaffian
        (fun e => logOrientation log e.val) M₀ u (fun e:Fin g.edges.length => w.getD e.val 0) := by
  rw [twistedEvaluation,characterValue_ofFn,
    referenceCoordinates_value cubic g hg rows R hrows log w M₀ hlen hmask,
    OccurrenceSkewCode.evaluate_eq_pairingPfaffian basis _ hg]
  unfold RotationRows.QuotientCoordinates.twistedPfaffian
  have hw : (fun e:Fin g.edges.length =>
      (twistedWeights (preparedOn cubic g rows log w) (List.ofFn u)).getD e.val 0)=
      twistWeights (SurfaceRawHomology.computedCoordinates g hg rows R hrows).encode u
        (fun e:Fin g.edges.length => w.getD e.val 0) := by
    funext e
    exact twistedWeights_get cubic g hg rows R hrows log w u e
  change _ * pairingPfaffian ((g.toMultiGraph hg).occurrenceSkewMatrix
    (fun e => logOrientation log e.val)
    (fun e => (twistedWeights (preparedOn cubic g rows log w) (List.ofFn u)).getD e.val 0))=_
  rw [hw]

end PlanarHom.SurfaceFKT
