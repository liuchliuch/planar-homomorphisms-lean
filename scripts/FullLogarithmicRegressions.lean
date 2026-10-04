import PlanarHom.FullLogarithmicPottsReduction
import PlanarHom.DomainFullLogarithmicAvailability

noncomputable section
open scoped BigOperators Topology Matrix.Norms.Operator
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.FullLogarithmicProductIdentities PlanarHom.PrescribedDomains
open PlanarHom.AlgebraicProductInterpolation

-- Negative logarithmic entries and a negative product coefficient are allowed.
private def signedLog : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = j then 0 else -1
example : ∀ i j, i ≠ j → signedLog i j ≠ 0 := by
  intro i j h
  simp [signedLog, h]
example : entryCoefficient signedLog 0 1 = -1 := by
  norm_num [entryCoefficient, signedLog]
example : (∏ _k : Fin 1, entryCoefficient signedLog (0 : Fin 3) (1 : Fin 3)) = -1 := by
  norm_num [entryCoefficient, signedLog]

-- Off-diagonal positions are counted, rather than signed or summed coefficients.
example : offDiagonalCount (fun k : Fin 3 => ((0 : Fin 3), k)) = 2 := by
  norm_num [offDiagonalCount, entryOrder, Fin.sum_univ_succ] <;> decide
example : (∏ k : Fin 3, (pottsMatrix : Matrix (Fin 3) (Fin 3) ℝ) 0 k) = 2 := by
  norm_num [pottsMatrix, Fin.prod_univ_succ]
example : (pottsMatrix : Matrix (Fin 3) (Fin 3) ℝ) =
    1 + Matrix.of (fun _ _ => 1) := pottsMatrix_eq_one_add_ones

-- The source-facing ordinary endpoint needs only nonzero logarithmic entries.
example (L : RealLanguage 3 2 1) (hunit : ∀ i, L.weights i = 1)
    (hA : (L.matrices 1).PosDef) (hnonneg : ∀ i j, 0 ≤ L.matrices 1 i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport (L.matrices 1) hA.1).Connected)
    (hlog : ∀ i j, i ≠ j → EntropyCompletion.matrixLog (L.matrices 1) i j ≠ 0)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction L.pottsTargetProblem base :=
  L.lemma311_reduction hunit 1 (by decide) hA hnonneg hconn hlog base available

private def domains311 (d : Fin 2) : Set (Fin 3) := if d = 0 then {0} else Set.univ
private def policy311 : Fin 2 → Fin 2 → Fin 2 → Prop := fun _ x y => x = 0 ∧ y = 0
private def unary311 : Fin 1 → Fin 2 → Prop := fun _ d => d = 0

-- Globality applies only to the selected matrix, leaving a companion restricted.
example : PathDomainTyping (withGlobalMatrix policy311 1) 1 1 0 1 :=
  withGlobalMatrix_pathTyping _ _ _ _ _
example : ¬withGlobalMatrix policy311 1 0 0 1 := by
  norm_num [withGlobalMatrix, policy311]

-- Full-domain metadata is used only for new path vertices; old domains can be proper.
example (L : RealLanguage 3 2 1) (hunit : ∀ i, L.weights i = 1)
    (hA : (L.matrices 1).PosDef) (hnonneg : ∀ i j, 0 ≤ L.matrices 1 i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport (L.matrices 1) hA.1).Connected)
    (hlog : ∀ i j, i ≠ j → EntropyCompletion.matrixLog (L.matrices 1) i j ≠ 0)
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction
      (L.domainProblem domains311 (withGlobalMatrix policy311 1) unary311) base) :
    PromisePolyTimeTuringReduction
      (L.domainPottsTargetProblem domains311 (withGlobalMatrix policy311 1) unary311 1) base :=
  L.lemma311_global_domain_reduction hunit domains311 policy311 unary311 1 1
    (by simp [domains311]) (by decide) hA hnonneg hconn hlog base available

#print axioms FullLogarithmicProductIdentities.productIdentities
#print axioms FullLogarithmicPottsReduction.homogeneous_reduction
#print axioms AlgebraicProductInterpolation.RealLanguage.lemma311_global_domain_reduction
