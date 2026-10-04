import PlanarHom.FullLogarithmicAvailability
import PlanarHom.RestrictedFixedSpectralTransfer
import PlanarHom.UniformDomainPowerSimulation
import PlanarHom.GlobalDomainSpectralAvailability

/-!
# Full logarithmic support with original prescribed domains

The source matrix must already permit the endpoint/full-domain path cases.
Under the canonical global-matrix interpretation this is automatic. Original
vertex domains and all companion permissions are retained, and private path
vertices receive an existing full-domain record. No source policy is broadened
by the reduction.
-/
noncomputable section
namespace PlanarHom.DomainFullLogarithmicAvailability
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases
open EffectiveProductTransfer FullLogarithmicProductIdentities
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {dimension q bt ut dt : ℕ}

def targetProblem (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) : PromiseProblem :=
  domainEvaluationProblem basis (appendOne M pottsMatrix) U (fun _ => 1)
    D (appendOne B (B old)) T

/-- The exact original raw domain promise, with the new target inheriting only
the existing selected source label's endpoint permissions. -/
theorem target_valid_iff (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (raw : Bits) :
    (targetProblem basis M U D B T old).valid raw ↔
      EncodedInput (appendOne B (B old)) T raw := Iff.rfl

/-- A fixed-target actual bit reduction with all intrinsic domain metadata. -/
def reduction_of_pathTyping (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfullDomain : D full = Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (hq : 3 ≤ q) (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hnonneg : ∀ i j, 0 ≤ SpectralFieldPresentation.realMatrix (M old) i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport
      (SpectralFieldPresentation.realMatrix (M old)) hA.1).Connected)
    (hfullLog : ∀ i j, i ≠ j →
      EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j ≠ 0) :
    PromisePolyTimeTuringReduction (targetProblem basis M U D B T old)
      (domainEvaluationProblem basis M U (fun _ => 1) D B T) := by
  let HT := EncodedGraph (appendOne B (B old)) T
  have hNonzero : ∀ n, q - 1 ≤ n → ∀ i j, (M old ^ n) i j ≠ 0 := by
    intro n hn i j hz
    have hp := FullLogarithmicAvailability.power_positive (M old) hA hnonneg hconn n hn i j
    rw [← matrixPowerFamily_coe _ hA.1, hz] at hp
    exact lt_irrefl 0 hp
  let r := RestrictedFixedSpectralTransfer.reduction basis M (extendedUnaries U D) (fun _ => 1)
    (fun n => M old ^ n) pottsMatrix HT
    (fun _ h => (h.planarValid _ T).1) (fun _ h s => h.parallelLabel _ T bt s)
    (q - 1) (by omega)
    (spectralCandidateCount q (Nat.card (spectrum ℝ (SpectralFieldPresentation.realMatrix (M old)))))
    (SpectralPowerEvaluationMachines.fp_matrixPowers basis (M old) hA.1) hNonzero
    (spectral_samples (M old) pottsMatrix hA (q - 1) pottsMatrix_symm
      (FullLogarithmicAvailability.identities (M old) hA hfullLog))
    (domainEvaluationProblem basis M U (fun _ => 1) D B T)
    (UniformDomainPowerSimulation.reduction basis M U D B T old full hfullDomain hpath)
  exact r.transport _ _
    (fun raw h => (encodedInput_iff_graph (appendOne B (B old)) T raw).mp h)
    (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl)

/-- For a source matrix already global on the ambient colors, all path typing
is justified by that same source policy, with no extra availability assumption. -/
def reduction_global (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfullDomain : D full = Set.univ)
    (hq : 3 ≤ q) (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hnonneg : ∀ i j, 0 ≤ SpectralFieldPresentation.realMatrix (M old) i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport
      (SpectralFieldPresentation.realMatrix (M old)) hA.1).Connected)
    (hfullLog : ∀ i j, i ≠ j →
      EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j ≠ 0) :
    PromisePolyTimeTuringReduction (targetProblem basis M U D (withGlobalMatrix B old) T old)
      (domainEvaluationProblem basis M U (fun _ => 1) D (withGlobalMatrix B old) T) :=
  reduction_of_pathTyping basis M U D (withGlobalMatrix B old) T old full hfullDomain
    (fun x y _ => withGlobalMatrix_pathTyping B old full x y)
    hq hA hnonneg hconn hfullLog

end PlanarHom.DomainFullLogarithmicAvailability

namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode PrescribedDomains
variable {q bt ut dt : ℕ} (L : RealLanguage q bt ut)

def domainPottsTargetProblem (D : Fin dt → Set (Fin q))
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop) (old : Fin bt) :
    PromiseProblem :=
  DomainFullLogarithmicAvailability.targetProblem L.basis L.matricesK L.unariesK D B T old

/-- Source-facing prescribed-domain Lemma 3.11, with exact original path typing. -/
def lemma311_domain_reduction (hunit : ∀ i, L.weights i = 1)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfullDomain : D full = Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (hq : 3 ≤ q) (hA : (L.matrices old).PosDef)
    (hnonneg : ∀ i j, 0 ≤ L.matrices old i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport (L.matrices old) hA.1).Connected)
    (hfullLog : ∀ i j, i ≠ j → EntropyCompletion.matrixLog (L.matrices old) i j ≠ 0)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction (L.domainPottsTargetProblem D B T old) base := by
  apply (DomainFullLogarithmicAvailability.reduction_of_pathTyping L.basis L.matricesK L.unariesK
    D B T old full hfullDomain hpath hq hA hnonneg hconn hfullLog).trans
  simpa only [RealLanguage.domainProblem, weightsK_eq_one L hunit] using available

/-- Canonical global-source policy wrapper retaining the supplied source availability. -/
def lemma311_global_domain_reduction (hunit : ∀ i, L.weights i = 1)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfullDomain : D full = Set.univ)
    (hq : 3 ≤ q) (hA : (L.matrices old).PosDef)
    (hnonneg : ∀ i j, 0 ≤ L.matrices old i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport (L.matrices old) hA.1).Connected)
    (hfullLog : ∀ i j, i ≠ j → EntropyCompletion.matrixLog (L.matrices old) i j ≠ 0)
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (L.domainProblem D (withGlobalMatrix B old) T) base) :
    PromisePolyTimeTuringReduction (L.domainPottsTargetProblem D (withGlobalMatrix B old) T old) base :=
  L.lemma311_domain_reduction hunit D (withGlobalMatrix B old) T old full hfullDomain
    (fun x y _ => withGlobalMatrix_pathTyping B old full x y) hq hA hnonneg hconn hfullLog base available

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
