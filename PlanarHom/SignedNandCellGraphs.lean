import PlanarHom.RoutingIncidencePlanarity
import PlanarHom.SignedNandFormulaIdentity

/-! Literal coalesced signed-NAND replacement graphs for the four fixed cell
kinds. The clause centers and every old Boolean variable are retained. -/
noncomputable section
open Classical
namespace PlanarHom.SignedNandCells
open PositiveBlockProgram ParsimoniousNorOneInThree MultiGraph IntegerStraightDrawing
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

abbrev Vertex (k : Kind) := Fin k.variableCount ⊕ Fin k.clauseCount

def vertexEquiv (k : Kind) : Vertex k ≃ Fin (k.variableCount+k.clauseCount) := finSumFinEquiv

def edgeCount : Kind → ℕ
  | .wire => 26
  | .cross => 72
  | .fan => 52
  | .test => 6

def edgeData (k : Kind) : Fin (edgeCount k) → Fin (k.variableCount+k.clauseCount) × Fin (k.variableCount+k.clauseCount) :=
  match k with
  | .wire => (![(0,2),(2,3),(0,3),(0,7),(2,7),(3,7),(1,2),(1,3),(1,8),(2,8),(3,8),(4,5),(3,5),(3,4),(4,9),(5,9),(3,9),(4,6),(3,6),(4,10),(6,10),(3,10),(5,6),(5,11),(4,11),(6,11)] : Fin 26 → Fin 12 × Fin 12)
  | .cross => (![(0,6),(5,6),(0,5),(0,17),(6,17),(5,17),(1,7),(5,7),(1,5),(1,18),(7,18),(5,18),(4,6),(6,7),(4,7),(4,19),(6,19),(7,19),(1,9),(8,9),(1,8),(1,20),(9,20),(8,20),(2,10),(8,10),(2,8),(2,21),(10,21),(8,21),(4,9),(9,10),(4,10),(4,22),(9,22),(10,22),(2,12),(11,12),(2,11),(2,23),(12,23),(11,23),(3,13),(11,13),(3,11),(3,24),(13,24),(11,24),(4,12),(12,13),(4,13),(4,25),(12,25),(13,25),(3,15),(14,15),(3,14),(3,26),(15,26),(14,26),(0,16),(14,16),(0,14),(0,27),(16,27),(14,27),(4,15),(15,16),(4,16),(4,28),(15,28),(16,28)] : Fin 72 → Fin 29 × Fin 29)
  | .fan => (![(0,3),(3,4),(0,4),(0,13),(3,13),(4,13),(1,3),(1,4),(1,14),(3,14),(4,14),(5,6),(4,6),(4,5),(5,15),(6,15),(4,15),(5,7),(4,7),(5,16),(7,16),(4,16),(6,7),(6,17),(5,17),(7,17),(0,8),(8,9),(0,9),(0,18),(8,18),(9,18),(2,8),(2,9),(2,19),(8,19),(9,19),(10,11),(9,11),(9,10),(10,20),(11,20),(9,20),(10,12),(9,12),(10,21),(12,21),(9,21),(11,12),(11,22),(10,22),(12,22)] : Fin 52 → Fin 23 × Fin 23)
  | .test => (![(0,1),(1,2),(0,2),(0,3),(1,3),(2,3)] : Fin 6 → Fin 4 × Fin 4)

def graph (k : Kind) : MultiGraph (Vertex k) (Fin (edgeCount k)) where
  src e := (vertexEquiv k).symm (edgeData k e).1
  dst e := (vertexEquiv k).symm (edgeData k e).2

def rawGraph (k : Kind) : MultiGraph (Vertex k) (Fin k.clauseCount × Fin 6) :=
  SignedNandFormulaIdentity.graph k.occurrence

/-- Every retained local edge is one of the literal K4 occurrence edges,
possibly with its orientation reversed. -/
theorem edge_sound (k : Kind) : ∀ e : Fin (edgeCount k),∃ c : Fin k.clauseCount,∃ j : Fin 6,
    ((graph k).src e=(rawGraph k).src (c,j) ∧ (graph k).dst e=(rawGraph k).dst (c,j)) ∨
    ((graph k).src e=(rawGraph k).dst (c,j) ∧ (graph k).dst e=(rawGraph k).src (c,j)) := by
  cases k <;> decide

/-- Coalescing loses no unordered adjacency. The separate algebraic NAND
idempotence theorem justifies removing its repeated occurrences. -/
theorem edge_coverage (k : Kind) : ∀ c : Fin k.clauseCount,∀ j : Fin 6,∃ e : Fin (edgeCount k),
    ((graph k).src e=(rawGraph k).src (c,j) ∧ (graph k).dst e=(rawGraph k).dst (c,j)) ∨
    ((graph k).src e=(rawGraph k).dst (c,j) ∧ (graph k).dst e=(rawGraph k).src (c,j)) := by
  cases k <;> decide

def basePoint (k : Kind) : Fin (k.variableCount+k.clauseCount) → Point :=
  match k with
  | .wire => ![(0,0),(64,0),(32,2),(32,12),(32,17),(24,20),(40,20),(20,5),(44,5),(29,16),(35,16),(32,19)]
  | .cross => ![(0,0),(0,64),(64,64),(64,0),(32,32),(8,32),(12,28),(12,36),(32,56),(28,52),(36,52),(56,32),(52,36),(52,28),(32,8),(36,12),(28,12),(8,24),(8,40),(16,32),(24,56),(40,56),(32,48),(56,40),(56,24),(48,32),(40,8),(24,8),(32,16)]
  | .fan => ![(0,0),(64,64),(64,0),(32,34),(32,44),(32,49),(24,44),(40,60),(32,2),(32,12),(32,17),(24,20),(40,20),(20,25),(44,49),(29,45),(35,51),(32,51),(20,5),(44,5),(29,16),(35,16),(32,19)]
  | .test => ![(0,128),(0,64),(0,0),(32,64)]

def point (s : CellShape) (v : Vertex s.kind) : Point :=
  let p := basePoint s.kind (vertexEquiv s.kind v)
  match s with
  | .wireTop => (p.1,64-p.2)
  | .wireBottom => p
  | .wireDown => (p.1,64-p.1-p.2)
  | .cross => p
  | .fan => (p.1,64-p.2)
  | .test => p

/-- The five non-test variants are actual integer straight-line drawings.
The collinear test ports are handled by a separate polygonal construction. -/
def straightCertificate (s : CellShape) (hs : s≠.test) : Certificate (graph s.kind) (point s) := by
  cases s
  all_goals first
  | exact False.elim (hs rfl)
  | exact {
    injective := by decide
    nondegenerate := by decide
    separated := by decide
    avoids := by decide }

def straightDrawing (s : CellShape) (hs : s≠.test) : PlaneDrawing (graph s.kind) :=
  IntegerStraightDrawing.drawing (straightCertificate s hs)

end PlanarHom.SignedNandCells
