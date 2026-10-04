import PlanarHom.SurfaceRawQuotientCoordinates
import PlanarHom.SurfaceFisherCodeMachines
import PlanarHom.SurfaceFisherMatchingMask
import PlanarHom.SurfaceBoundedCharacters
import PlanarHom.OccurrenceSkewCodeSemantics
import PlanarHom.FisherIsingCodeIdentity

/-! NEW complete total supplied-surface Ising program. Character enumeration
is capped by the fixed ambient genus. Calibration is materialized once, using
one support Pfaffian per character, and the weighted transform then uses one
further Pfaffian per character. -/
namespace PlanarHom.SurfaceFKT
open Complexity SurfaceBooleanRows
variable {K : Type} [Field K] [DecidableEq K]

structure Prepared (K : Type) where
  cubic : MixedCode
  graph : MixedCode
  orientation : List ℕ
  weights : List K
  quotient : QuotientData

def prepare (ρ : K) (g : MixedCode) (rows : PlanarityRowFaceCode.Rows) : Prepared K where
  cubic := SurfaceFisherCode.intermediate g rows
  graph := SurfaceFisherCode.code g rows
  orientation := SurfaceFisherCode.orientationLog g rows
  weights := SurfaceFisherCode.weights ρ g rows
  quotient := SurfaceRawHomology.data (SurfaceFisherCode.code g rows) (SurfaceFisherCode.inheritedRows g rows)

def characterValue (u x : Row) : K :=
  (u.zipIdx.map (fun p => if p.1 && bitAt x p.2 then (-1:K) else 1)).prod

def characters (ambient : ℕ) (p : Prepared K) : List Row := boundedWords (2*ambient) p.quotient.2.length

def supportWeights (p : Prepared K) (x : Row) : List K :=
  (SurfaceFisherMatching.mask p.cubic (liftQuotient p.quotient x)).map (fun b => if b then 1 else 0)

def calibration (p : Prepared K) (x : Row) : K :=
  PfaffianList.evaluateGrid (OccurrenceSkewCode.grid (p.graph,(p.orientation,supportWeights p x)))

def calibrationTable (ambient : ℕ) (p : Prepared K) : List (Row×K) :=
  (characters ambient p).map (fun x => (x,calibration p x))

def walsh (table : List (Row×K)) (u : Row) : K :=
  (table.map (fun p => characterValue u p.1*p.2)).sum

def referenceCoordinates (p : Prepared K) : Row :=
  encodeQuotient p.quotient (SurfaceFisherMatching.mask p.cubic [])

def twistedWeights (p : Prepared K) (u : Row) : List K :=
  p.graph.edges.zipIdx.map (fun e => p.weights[e.2]?.getD 0 *
    characterValue u (encodeQuotient p.quotient (unit (SurfaceRawHomology.shape p.graph) e.2)))

def twistedEvaluation (p : Prepared K) (u : Row) : K :=
  characterValue u (referenceCoordinates p) *
    PfaffianList.evaluateGrid (OccurrenceSkewCode.grid (p.graph,(p.orientation,twistedWeights p u)))

def reciprocalDimension (p : Prepared K) : K := (p.quotient.2.map (fun _ => (2:K)⁻¹)).prod

def matchingValue (ambient : ℕ) (p : Prepared K) : K :=
  let table := calibrationTable ambient p
  reciprocalDimension p*(table.map (fun t => walsh table t.1*twistedEvaluation p t.1)).sum

def value (ambient : ℕ) (ρ : K) (g : MixedCode) (rows : PlanarityRowFaceCode.Rows) : K :=
  FisherCodePipeline.normalization ρ g*matchingValue ambient (prepare ρ g rows)

end PlanarHom.SurfaceFKT
