import PlanarHom.RectangularCoreSourceCoordinates
import PlanarHom.CommonCubeChartBasicConsequences

/-! Exact conditional version of the concrete original-source entrance.
The all-size Potts hardness foundation is an explicit parameter here;
it is discharged by `PositivePottsFoundationClosed` in the closed endpoints;
all X/Y source access, physical Gram seeds and common-chart construction are real. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularCoreSourceEntrance
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteContext TypedSideSourceAccess ClosedMatrixFamily Complexity
open RectangularSourceNormSimulation (block)
variable {x y : ℕ}

theorem source_common_charts_of_potts [Nonempty (Fin x)] [Nonempty (Fin y)]
    (hPotts : PositivePottsFoundation)
    (L : RealLanguage (x+y) 1 0) (hunit : ∀i,L.weights i=1)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀i j,0<B i j)
    (hM : L.matrices 0=block B)
    (hrows : ∀i j,i≠j→∀t:ℝ,B i≠t•B j)
    (hcolumns : ∀i j,i≠j→∀t:ℝ,B.transpose i≠t•B.transpose j)
    (hnot : ¬PromisedSharpPHard L.problem) :
    Nonempty (CommonCubeChart (xFamily (fun _:Fin 1=>crossFin B) (fun _=>crossPolicy))) ∧
    Nonempty (CommonCubeChart (yFamily (fun _:Fin 1=>crossFin B) (fun _=>crossPolicy))) := by
  have ha:=source_algebraic L B hM
  have hf:=source_contains L B hM
  have hc:=source_crosses L B hM
  exact ⟨common_x_chart_from_homogeneous_generator_of_potts hPotts _ _ ha 0 L hunit hf hc
      B hB hrows rfl rfl hnot,
    common_y_chart_from_homogeneous_generator_of_potts hPotts _ _ ha 0 L hunit hf hc
      B hB hcolumns rfl rfl hnot⟩

end PlanarHom.RectangularCoreSourceEntrance
