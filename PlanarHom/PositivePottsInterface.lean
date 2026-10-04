import PlanarHom.PromisedSharpPHardness
import PlanarHom.HammingPottsToSource
import PlanarHom.UnitBackgroundLanguage

/-! NEW explicit all-size positive-Potts interface matching the surviving
conditional consumers. Its hardness theorem is not postulated or proved here.
The rational problem is literal I+J on ordinary planar raw inputs. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FullLogarithmicProductIdentities

def pottsRationalBasis : Module.Basis (Fin 1) ℚ ℚ := Module.Basis.singleton (Fin 1) ℚ

def pottsRationalProblem (q : ℕ) : PromiseProblem :=
  evaluationProblem pottsRationalBasis (fun _ : Fin 1=>(pottsMatrix : Matrix (Fin q) (Fin q) ℚ))
    (fun u : Fin 0=>u.elim0) (fun _=>1)

/-- The exact external premise needed by the conditional common-cube theorem.
No witness of this proposition is introduced by this definition. -/
def PositivePottsFoundation : Prop := ∀q,3≤q→PromisedSharpPHard (pottsRationalProblem q)

/-- A genuine compiled output-field descent reduction, preserving every raw
planar graph input and converting the embedded rational answer exactly. -/
def pottsFieldReduction {K : IntermediateField ℚ ℝ} {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (q : ℕ) :
    PromisePolyTimeTuringReduction (pottsRationalProblem q)
      (FullLogarithmicPottsReduction.pottsProblem basis q) := by
  let φ : ℚ→ₐ[ℚ] K:=Algebra.ofId ℚ K
  let M:=fun _ : Fin 1=>(pottsMatrix : Matrix (Fin q) (Fin q) ℚ)
  let U : Fin 0→Fin q→ℚ:=fun u=>u.elim0
  have hm : (fun l i j=>φ (M l i j)) =
      (fun _ : Fin 1=>(pottsMatrix : Matrix (Fin q) (Fin q) K)) := by
    funext l i j
    dsimp [M,pottsMatrix]
    split_ifs
    · exact map_ofNat φ 2
    · exact map_one φ
  have hu : (fun l i=>φ (U l i)) = (fun u : Fin 0=>u.elim0) := by
    funext u
    exact u.elim0
  have hw : (fun _ : Fin q=>φ (1:ℚ)) = (fun _=>1) := by simp
  have r:=fieldDescentReduction pottsRationalBasis basis φ M U (fun _=>1)
  simpa only [pottsRationalProblem,FullLogarithmicPottsReduction.pottsProblem,hm,hu,hw] using r

theorem positivePottsField_hard (hPotts : PositivePottsFoundation)
    {K : IntermediateField ℚ ℝ} {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (q : ℕ) (hq : 3≤q) :
    PromisedSharpPHard (FullLogarithmicPottsReduction.pottsProblem basis q) :=
  (hPotts q hq).trans (pottsFieldReduction basis q)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
