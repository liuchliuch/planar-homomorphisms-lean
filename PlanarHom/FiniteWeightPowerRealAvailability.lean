import PlanarHom.DomainFiniteWeightPowerClosure

/-! Source-facing finite-family source3.7 closure: literal real algebraic data,
all original companions, one supplied source availability and exact real sums. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases PositiveWeightRemoval
variable {q bt ut n dt : ℕ} (L : RealLanguage q bt ut)

def finiteWeightPowerProblem (hw : ∀i,0<L.weights i) (rs : Fin n→ℚ) : PromiseProblem :=
  evaluationProblem (finitePowerBasis L.weightsK hw rs) (finitePowerMatrices L.matricesK L.weightsK rs)
    (finitePowerUnaryLanguage L.unariesK L.weightsK rs)
    (fun i=>sourceInclusion L.field (finitePowerAlphabet L.weightsK rs) (L.weightsK i))

def domainFiniteWeightPowerProblem (D : Fin dt→Set (Fin q))
    (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (old : Fin bt) (hw : ∀i,0<L.weights i) (rs : Fin n→ℚ) : PromiseProblem :=
  domainEvaluationProblem (finitePowerBasis L.weightsK hw rs)
    (finitePowerMatrices L.matricesK L.weightsK rs) (finitePowerUnaryLanguage L.unariesK L.weightsK rs)
    (fun i=>sourceInclusion L.field (finitePowerAlphabet L.weightsK rs) (L.weightsK i)) D
    (appendFamily B (fun _ : Fin n=>B old)) (appendFamily T (fun (_ : Fin n) _=>True))

/-- All prescribed rational exponents, including negative and zero values,
coexist with the entire source language and use the very same source oracle. -/
def lemma37_finiteRationalPowers (old : Fin bt)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hw : ∀i,0<L.weights i) (hnonzero : ∀i,L.matrices old i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (rs : Fin n→ℚ) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction (L.finiteWeightPowerProblem hw rs) base :=
  (finiteRationalDiagonalUnaryReduction L.basis L.matricesK L.unariesK L.weightsK
    old hs hw hnonzero hproj rs).trans available

/-- Domain-aware finite-family closure retains every original domain set and
companion policy. No singleton-domain or pinning availability is assumed. -/
def lemma37_domainFiniteRationalPowers (D : Fin dt→Set (Fin q))
    (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : D full=Set.univ) (hglobal : ∀x y,B old x y)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hw : ∀i,0<L.weights i) (hnonzero : ∀i,L.matrices old i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (rs : Fin n→ℚ) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction (L.domainFiniteWeightPowerProblem D B T old hw rs) base :=
  (domainFiniteRationalDiagonalUnaryReduction L.basis L.matricesK L.unariesK L.weightsK
    D B T old full hfull hglobal hs hw hnonzero hproj rs).trans available

/-- Coercing the common-field answer gives exactly the original real weighted
partition function with every diagonal and its unary present simultaneously. -/
theorem finiteWeightPower_evaluate_coe (rs : Fin n→ℚ)
    (g : MixedCode) (hg : g.Valid (bt+n) (ut+n)) :
    (extensionField L.field (finitePowerAlphabet L.weightsK rs)).val
      (g.evaluate hg (finitePowerMatrices L.matricesK L.weightsK rs)
        (finitePowerUnaryLanguage L.unariesK L.weightsK rs)
        (fun i=>sourceInclusion L.field (finitePowerAlphabet L.weightsK rs) (L.weightsK i))) =
      g.evaluate hg (appendFamily L.matrices (fun l=>diagonalPower L.weights (rs l)))
        (appendFamily L.unaries (fun l i=>L.weights i^(rs l : ℝ))) L.weights :=
  L.mixedFiniteTarget_evaluate_coe (finitePowerDiagonals L.weightsK rs)
    (finitePowerUnaries L.weightsK rs) g hg

/-- The exact real-sum identification keeps the prescribed domain at every
original vertex, including any narrow domain in the original instance. -/
theorem finiteWeightPower_evaluateRestricted_coe (rs : Fin n→ℚ)
    (g : MixedCode) (hg : g.Valid (bt+n) (ut+n))
    (D : Fin dt→Set (Fin q)) (δ : Fin g.vertices→Fin dt) :
    (extensionField L.field (finitePowerAlphabet L.weightsK rs)).val
      (PrescribedDomains.evaluateRestricted g hg (finitePowerMatrices L.matricesK L.weightsK rs)
        (finitePowerUnaryLanguage L.unariesK L.weightsK rs)
        (fun i=>sourceInclusion L.field (finitePowerAlphabet L.weightsK rs) (L.weightsK i)) D δ) =
      PrescribedDomains.evaluateRestricted g hg
        (appendFamily L.matrices (fun l=>diagonalPower L.weights (rs l)))
        (appendFamily L.unaries (fun l i=>L.weights i^(rs l : ℝ))) L.weights D δ :=
  L.mixedFiniteTarget_evaluateRestricted_coe (finitePowerDiagonals L.weightsK rs)
    (finitePowerUnaries L.weightsK rs) g hg D δ

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
