import PlanarHom.SingleSideSourceReduction
import PlanarHom.TypedSideCommonChartSeed
import PlanarHom.AvailableCommonCubeChart
import PlanarHom.AvailablePositiveUnitCore

/-! NEW concrete ordinary-source realization of a closed matrix family. The
existing typed programs are specialized to all original colors on one side;
the empty other side is handled by SingleSideSourceReduction's actual machine. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity TypedBipartiteContext TypedBipartiteSpectral TypedSideSourceAccess
open ClosedMatrixFamily
variable {q : ℕ}

def ordinaryFamily (L : RealLanguage q 1 0) : Set (Matrix (Fin q) (Fin q) ℝ) :=
  xFamily (y:=0) L.matrices (fun _=>sameX)

theorem zeroExtend_empty (N : Matrix (Fin q) (Fin q) ℝ) : zeroExtendFin (y:=0) N = N := by
  ext i j
  exact zeroExtendFin_left N i j

theorem ordinaryFamily_generator (L : RealLanguage q 1 0) (hs : (L.matrices 0).IsHermitian) :
    L.matrices 0 ∈ L.ordinaryFamily := by
  refine ⟨hs,?_⟩
  rw [zeroExtend_empty]
  exact typed_contextual_generator (domains q 0) L.matrices (fun _=>sameX) L.matrices_algebraic 0

theorem ordinaryFamily_algebraic (L : RealLanguage q 1 0) :
    AlgebraicSourceClosed L.ordinaryFamily :=
  xFamily_algebraicSourceClosed (y:=0) L.matrices (fun _=>sameX)

theorem ordinaryFamily_effective (L : RealLanguage q 1 0) :
    EffectiveSpectralClosed L.ordinaryFamily :=
  xFamily_effectiveClosed (y:=0) L.matrices (fun _=>sameX)

theorem ordinaryFamily_gadgets (L : RealLanguage q 1 0) :
    MixedPlanarGadgetClosed L.ordinaryFamily :=
  xFamily_mixedPlanarGadgetClosed (y:=0) L.matrices (fun _=>sameX)

def ordinaryFamily_source (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : N ∈ L.ordinaryFamily) :
    PromisePolyTimeTuringReduction
      (unitLanguage (fun _:Fin 1=>N) (fun _=>L.ordinaryFamily_algebraic.algebraic N hN)).problem
      L.problem := by
  have hcontains : L.ContainsTypedMatrices (fun _:Fin 1=>sameX) L.matrices (fun _=>sameX) :=
    ⟨id,fun _=>⟨rfl,rfl⟩⟩
  have r := SingleSideSourceReduction.reduction L.basis L.matricesK L.unariesK L.weightsK
    (fun _:Fin 1=>sameX) (fun u:Fin 0=>u.elim0)
  exact xFamily_singleSourceReduction (y:=0) L.matrices (fun _=>sameX) L
    (fun _:Fin 1=>sameX) (fun u:Fin 0=>u.elim0) hunit hcontains L.problem r N hN

theorem ordinaryFamily_common_chart (hPotts : PositivePottsFoundation)
    (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (hne : ∃H,Admissible L.ordinaryFamily H) (hnot : ¬PromisedSharpPHard L.problem) :
    Nonempty (CommonCubeChart L.ordinaryFamily) :=
  exists_common_cube_chart hPotts L.ordinaryFamily L.ordinaryFamily_algebraic
    L.ordinaryFamily_effective L.ordinaryFamily_gadgets L.problem
    (fun N hN=>⟨L.ordinaryFamily_source hunit N hN⟩) hne hnot

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
