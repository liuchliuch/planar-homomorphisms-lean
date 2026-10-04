import PlanarHom.ConnectedColorRestrictionReduction
import PlanarHom.GraphComponentReduction

/-! Arbitrary planar inputs reduce from any source-support color component to
the original homogeneous weighted oracle, by actual component processing. -/
noncomputable section
open Classical
namespace PlanarHom.RootedRestriction
open Complexity Complexity.MixedCode
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable [LinearOrder K] [IsStrictOrderedRing K] {dimension : ℕ}

/-- Input connected components are computed, not supplied as advice. The empty
input gives one; every isolate is retained. -/
def submatrixReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (hs : ∀ i j,M i j=M j i) (w : C → K) (hw : ∀ i,0<w i)
    (X : Set C) (hX : ColorClosed M X) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => fun i j : X => M i.val j.val)
        (fun u : Fin 0 => Fin.elim0 u) (fun i : X => w i.val))
      (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w) :=
  (GraphComponentCode.componentReduction basis (fun _ : Fin 1 => fun i j : X => M i.val j.val)
    (fun u : Fin 0 => Fin.elim0 u) (fun i : X => w i.val)).trans
      (connectedSubmatrixReduction basis M hs w hw X hX)

/-- Source3.5's component extraction for each actual numerical support component. -/
def supportComponentReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (hs : ∀ i j,M i j=M j i) (w : C → K) (hw : ∀ i,0<w i)
    (c : (colorSupport M hs).ConnectedComponent) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => fun i j : c.supp => M i.val j.val)
        (fun u : Fin 0 => Fin.elim0 u) (fun i : c.supp => w i.val))
      (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w) :=
  submatrixReduction basis M hs w hw c.supp (component_colorClosed M hs c)

end PlanarHom.RootedRestriction
