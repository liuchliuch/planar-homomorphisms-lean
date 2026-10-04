import PlanarHom.FullLogarithmicAvailability
import PlanarHom.MixedLabelAliasReductions
import PlanarHom.RootedHomogeneousSemantics

/-!
# The literal homogeneous Potts-to-source reduction

Source Lemma 3.11 first proves Pl-GH(I_q+J_q) ≤ Pl-GH(M), then cites
Proposition 2.2(ii). This module proves that actual reduction, with the original
field answer presentation, and also its version for a larger available language.

The remaining external input is hardness of the homogeneous planar problem
`pottsProblem basis` for q ≥ 3 (including its exact answer-code convention).
The source derives that input from the planar Tutte classification [Ver05] at
(q+1,2), using Z_(I+J)(G) = q^c(G) T_G(q+1,2). Neither that classification nor
an unconditional #P-hardness theorem is asserted or postulated here.
-/
noncomputable section
namespace PlanarHom.FullLogarithmicPottsReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases FullLogarithmicProductIdentities
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {q bt ut dimension : ℕ}

/-- One edge label, no unary labels, unit vertex weights, and ordinary planar raw inputs. -/
def pottsProblem (basis : Module.Basis (Fin dimension) ℚ K) (q : ℕ) : PromiseProblem :=
  evaluationProblem basis (fun _ : Fin 1 => (pottsMatrix : Matrix (Fin q) (Fin q) K))
    (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1)

/-- Its decoded value is literally the graph partition function for I_q+J_q. -/
theorem evaluate_potts (g : MixedCode) (hg : g.Valid 1 0) :
    g.evaluate hg (fun _ : Fin 1 => (pottsMatrix : Matrix (Fin q) (Fin q) K))
      (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1) =
      (g.toMultiGraph hg).partition
        (1 + Matrix.of (fun _ _ => (1 : K)) : Matrix (Fin q) (Fin q) K) (fun _ => 1) := by
  rw [evaluate_homogeneous, pottsMatrix_eq_one_add_ones]

/-- Homogeneous inputs embed into the joint target by actual finite-label
machines; no availability of pinning or of a unary constraint is assumed. -/
def toJointTarget (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) :
    PromisePolyTimeTuringReduction (pottsProblem basis q)
      (evaluationProblem basis (appendOne M pottsMatrix) U (fun _ => 1)) := by
  have rb : PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => (pottsMatrix : Matrix (Fin q) (Fin q) K)) U (fun _ => 1))
      (evaluationProblem basis (appendOne M pottsMatrix) U (fun _ => 1)) := by
    simpa only [Function.comp_def, appendOne_aux] using
      binaryRelabelReduction basis (fun _ : Fin 1 => Fin.last bt)
        (appendOne M pottsMatrix) U (fun _ => 1)
  have ru := unaryRelabelReduction basis (fun u : Fin 0 => Fin.elim0 u)
    (fun _ : Fin 1 => (pottsMatrix : Matrix (Fin q) (Fin q) K)) U (fun _ => 1)
  have he : U ∘ (fun u : Fin 0 => Fin.elim0 u) = (fun u : Fin 0 => Fin.elim0 u) := by
    funext u
    exact Fin.elim0 u
  rw [he] at ru
  exact ru.trans rb

/-- Literal source 3.11 Potts reduction into an arbitrary original mixed language. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (hq : 3 ≤ q) (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hnonneg : ∀ i j, 0 ≤ SpectralFieldPresentation.realMatrix (M old) i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport
      (SpectralFieldPresentation.realMatrix (M old)) hA.1).Connected)
    (hfull : ∀ i j, i ≠ j →
      EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j ≠ 0) :
    PromisePolyTimeTuringReduction (pottsProblem basis q)
      (evaluationProblem basis M U (fun _ => 1)) :=
  (toJointTarget basis M U).trans
    (FullLogarithmicAvailability.reduction basis M U old hq hA hnonneg hconn hfull)

/-- In particular, the source may be exactly the one matrix M from the paper. -/
def homogeneous_reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K)
    (hq : 3 ≤ q) (hM : (SpectralFieldPresentation.realMatrix M).PosDef)
    (hnonneg : ∀ i j, 0 ≤ SpectralFieldPresentation.realMatrix M i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport
      (SpectralFieldPresentation.realMatrix M) hM.1).Connected)
    (hfull : ∀ i j, i ≠ j →
      EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix M) i j ≠ 0) :
    PromisePolyTimeTuringReduction (pottsProblem basis q)
      (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1)) :=
  reduction basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) 0 hq hM hnonneg hconn hfull

/-- This is the exact composition point for a separately proved Potts-hardness
reduction. Its external premise is visible and is not an axiom. -/
def transfer_external_potts_reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (hq : 3 ≤ q) (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hnonneg : ∀ i j, 0 ≤ SpectralFieldPresentation.realMatrix (M old) i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport
      (SpectralFieldPresentation.realMatrix (M old)) hA.1).Connected)
    (hfull : ∀ i j, i ≠ j →
      EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j ≠ 0)
    (target base : PromiseProblem)
    (pottsReduction : PromisePolyTimeTuringReduction target (pottsProblem basis q))
    (available : PromisePolyTimeTuringReduction (evaluationProblem basis M U (fun _ => 1)) base) :
    PromisePolyTimeTuringReduction target base :=
  (pottsReduction.trans (reduction basis M U old hq hA hnonneg hconn hfull)).trans available

end PlanarHom.FullLogarithmicPottsReduction

namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode
variable {q bt ut : ℕ} (L : RealLanguage q bt ut)

/-- Literal homogeneous I_q+J_q target with the source's exact algebraic answer presentation. -/
def lemma311_potts_reduction (hunit : ∀ i, L.weights i = 1) (old : Fin bt)
    (hq : 3 ≤ q) (hA : (L.matrices old).PosDef)
    (hnonneg : ∀ i j, 0 ≤ L.matrices old i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport (L.matrices old) hA.1).Connected)
    (hfull : ∀ i j, i ≠ j → EntropyCompletion.matrixLog (L.matrices old) i j ≠ 0)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction (FullLogarithmicPottsReduction.pottsProblem L.basis q) base := by
  apply (FullLogarithmicPottsReduction.reduction L.basis L.matricesK L.unariesK old
    hq hA hnonneg hconn hfull).trans
  simpa only [RealLanguage.problem, weightsK_eq_one L hunit] using available

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
