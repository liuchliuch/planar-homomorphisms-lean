import PlanarHom.IntegerStraightDrawing
import PlanarHom.ParsimoniousNorOneInThree
import Mathlib.Algebra.BigOperators.Fin

/-! A literal planar K4 clause for signed independent sets. The three boundary
vertices have unit activity; the center has activity -1. Summing the center
cancels the all-false input and retains exactly one occupied boundary vertex. -/
noncomputable section
namespace PlanarHom.SignedNandExactOneClause
open Classical MultiGraph ParsimoniousNorOneInThree
open scoped BigOperators

/-- Boundary triangle followed by its three edges to the marked center. -/
def graph : MultiGraph (Fin 4) (Fin 6) where
  src := ![0,1,2,0,1,2]
  dst := ![1,2,0,3,3,3]

def integerPoint : Fin 4 → IntegerStraightDrawing.Point :=
  ![(-3,0),(3,0),(0,3),(0,1)]

def integerCertificate : IntegerStraightDrawing.Certificate graph integerPoint where
  injective := by decide +kernel
  nondegenerate := by decide +kernel
  separated := by decide +kernel
  avoids := by decide +kernel

def drawing : PlaneDrawing graph := IntegerStraightDrawing.drawing integerCertificate

theorem planar : graph.Planar := ⟨drawing⟩

variable {R : Type*} [CommRing R]

def nandWeight (x y : Bool) : R := if x && y then 0 else 1

def centerActivity (z : Bool) : R := if z then -1 else 1

def extension (x y z t : Bool) : Fin 4 → Bool := ![x,y,z,t]

/-- This is the ordinary product over all six actual graph edge occurrences
and the one marked unary, not a separately postulated clause relation. -/
def term (col : Fin 4 → Bool) : R :=
  (∏ e : Fin 6, nandWeight (col (graph.src e)) (col (graph.dst e))) *
    centerActivity (col 3)

theorem term_eq (x y z t : Bool) : term (R:=R) (extension x y z t)=
    nandWeight x y*nandWeight y z*nandWeight z x*
      nandWeight x t*nandWeight y t*nandWeight z t*centerActivity t := by
  simp [term,graph,extension,Fin.prod_univ_succ]
  ring

/-- Exact signed multiplicity: 1 for each satisfying boundary input and 0 for
each other input. This equality holds over every commutative ring. -/
theorem center_sum (x y z : Bool) :
    (∑ t : Bool,term (R:=R) (extension x y z t))=
      if ExactlyOne x y z then 1 else 0 := by
  cases x <;> cases y <;> cases z <;>
    simp [Fintype.sum_bool,term_eq,nandWeight,centerActivity,ExactlyOne]

/-- The same identity with three ports given as a finite tuple. -/
theorem port_sum (b : Fin 3 → Bool) :
    (∑ t : Bool,term (R:=R) (extension (b 0) (b 1) (b 2) t))=
      if ExactlyOne (b 0) (b 1) (b 2) then 1 else 0 := center_sum _ _ _

/-- An unsatisfied zero-occupied clause has two opposite signed extensions. -/
theorem zero_boundary_cancellation :
    term (R:=R) (extension false false false false)=1 ∧
    term (R:=R) (extension false false false true)= -1 := by
  simp [term_eq,nandWeight,centerActivity]
end PlanarHom.SignedNandExactOneClause
