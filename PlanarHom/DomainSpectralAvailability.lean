import PlanarHom.DomainSpectralAppendReduction
import PlanarHom.SpectralRealAvailability

/-! Source-facing spectral availability with the original prescribed domains.
A fixed algebraic overfield supplies the actual CFC spectral data, and the
source oracle retains its original answer basis through an exact converter. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.SpectralAvailability
open Complexity Complexity.MixedCode FiniteLanguageAliases ProductCompatibility
open SpectralFieldPresentation PrescribedDomains
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q bt ut dt dimension : ℕ}

/-- CFC joint availability on the exact prescribed-domain promise. -/
def domainCfcAppendOverfieldReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (hC : (realMatrix (M old)).IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ x ∈ spectrum ℝ (realMatrix (M old)), IsAlgebraic ℚ (f x))
    (hzero : ∀ i, RealSpectralInterpolation.scalar (realMatrix (M old)) i=0 →
      f (RealSpectralInterpolation.scalar (realMatrix (M old)) i)=0)
    (hcompat : Compatible (RealSpectralInterpolation.scalar (realMatrix (M old)))
      (fun i => f (RealSpectralInterpolation.scalar (realMatrix (M old)) i))) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem (basis (M old) hC f hf)
        (appendOne (fun l i j => inclusion (M old) f (M l i j)) (N (M old) f))
        (fun l i => inclusion (M old) f (U l i)) (fun _ => 1) D (appendOne B (B old)) T)
      (domainEvaluationProblem b₀ M U (fun _ => 1) D B T) := by
  let C := M old
  let φ := inclusion C f
  let bF := basis C hC f hf
  let MF : Fin bt → Matrix (Fin q) (Fin q) (field C f) := fun l i j => φ (M l i j)
  let UF : Fin ut → Fin q → field C f := fun l i => φ (U l i)
  have hp : ∀ n : ℕ, 0<n → MF old ^ n = ∑ i, a C f i ^ n • P C f i := by
    intro n _
    exact sourceMatrix_pow C hC f n
  let first := domainSpectralAppendReduction bF MF UF D B T old full hfull hpath
    (P C f) (a C f) (b C f) hp (zero_lift C f hzero) (compatible_lift C f hcompat)
  have second : PromisePolyTimeTuringReduction
      (domainEvaluationProblem bF MF UF (fun _ => 1) D B T)
      (domainEvaluationProblem b₀ M U (fun _ => 1) D B T) := by
    simpa only [map_one] using domainFieldMapReduction b₀ bF φ M U (fun _ => 1) D B T
  have result := first.trans second
  change PromisePolyTimeTuringReduction
    (domainEvaluationProblem bF (appendOne MF (N C f)) UF (fun _ => 1) D (appendOne B (B old)) T) _
  rw [N_eq_sum C f]
  exact result

/-- PSD range projection, with no new permitted domain or pinning language. -/
def domainRangeAppendOverfieldReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (hC : (realMatrix (M old)).PosSemidef) :=
  domainCfcAppendOverfieldReduction b₀ M U D B T old full hfull hpath hC.1
    rangeFunction (rangeFunction_algebraic _) (rangeFunction_zero _) (rangeFunction_compatible _ hC)

/-- Every fixed rational exponent is permitted for a positive-definite source. -/
def domainRationalPowerAppendOverfieldReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (hC : (realMatrix (M old)).PosDef) (r : ℚ) :=
  domainCfcAppendOverfieldReduction b₀ M U D B T old full hfull hpath hC.1
    (fun x => x ^ (r : ℝ)) (powerFunction_algebraic _ hC r) (powerFunction_zero _ hC r)
    (PositiveUnaryRationalPowers.compatible_real_rpow _ (RealSpectralInterpolation.scalar_pos _ hC) r)

/-- Compose PSD range availability with the original fixed-field source oracle.
Original endpoint domains may be narrower than `full`; only the four actual
path endpoint pairs are required to be permitted. -/
def domainRangeAppendOverfield_joint (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (hC : (realMatrix (M old)).PosSemidef) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction
      (domainEvaluationProblem b₀ M U (fun _ => 1) D B T) base) :=
  (domainRangeAppendOverfieldReduction b₀ M U D B T old full hfull hpath hC).trans available

/-- Rational-power availability retaining the original endpoint domains and
requiring precisely the path typing used by the concrete queries. -/
def domainRationalPowerAppendOverfield_joint (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (hC : (realMatrix (M old)).PosDef) (r : ℚ) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction
      (domainEvaluationProblem b₀ M U (fun _ => 1) D B T) base) :=
  (domainRationalPowerAppendOverfieldReduction b₀ M U D B T old full hfull hpath hC r).trans available

end PlanarHom.SpectralAvailability

namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases
open SpectralFieldPresentation SpectralAvailability PrescribedDomains
variable {q bt ut dt : ℕ} (L : RealLanguage q bt ut)

def domainRangeTargetProblem (D : Fin dt → Set (Fin q))
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (old : Fin bt) (hC : (L.matrices old).PosSemidef) : PromiseProblem :=
  domainEvaluationProblem
    (SpectralFieldPresentation.basis (L.matricesK old) hC.1 rangeFunction (rangeFunction_algebraic _))
    (appendOne (fun l i j => inclusion (L.matricesK old) rangeFunction (L.matricesK l i j))
      (N (L.matricesK old) rangeFunction))
    (fun l i => inclusion (L.matricesK old) rangeFunction (L.unariesK l i)) (fun _ => 1)
    D (appendOne B (B old)) T

def domainRationalPowerTargetProblem (D : Fin dt → Set (Fin q))
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (old : Fin bt) (hC : (L.matrices old).PosDef) (r : ℚ) : PromiseProblem :=
  domainEvaluationProblem
    (SpectralFieldPresentation.basis (L.matricesK old) hC.1 (fun x => x ^ (r : ℝ)) (powerFunction_algebraic (L.matricesK old) hC r))
    (appendOne (fun l i j => inclusion (L.matricesK old) (fun x => x ^ (r : ℝ)) (L.matricesK l i j))
      (N (L.matricesK old) (fun x => x ^ (r : ℝ))))
    (fun l i => inclusion (L.matricesK old) (fun x => x ^ (r : ℝ)) (L.unariesK l i)) (fun _ => 1)
    D (appendOne B (B old)) T

/-- PSD range-projector availability under the explicit path-typing condition.
Every original domain assignment is retained, including narrower endpoint
domains. Only the private path vertices receive the prescribed full domain. -/
def lemma33_domain_range_of_pathTyping (hunit : ∀ i, L.weights i=1)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (hC : (L.matrices old).PosSemidef) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction (L.domainRangeTargetProblem D B T old hC) base := by
  apply domainRangeAppendOverfield_joint L.basis L.matricesK L.unariesK D B T old full hfull hpath hC base
  simpa only [RealLanguage.domainProblem,weightsK_eq_one L hunit] using available

/-- Every fixed rational spectral power under the explicit path-typing
condition, with unchanged original endpoint domains and source availability. -/
def lemma33_domain_rationalPower_of_pathTyping (hunit : ∀ i, L.weights i=1)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (hC : (L.matrices old).PosDef) (r : ℚ) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction (L.domainRationalPowerTargetProblem D B T old hC r) base := by
  apply domainRationalPowerAppendOverfield_joint L.basis L.matricesK L.unariesK D B T old full hfull hpath hC r base
  simpa only [RealLanguage.domainProblem,weightsK_eq_one L hunit] using available

/-- Specialized full/full-endpoint corollary. Its stronger endpoint hypothesis
implies path typing; it is not a closure assertion for arbitrary endpoint tables. -/
def lemma33_domain_range (hunit : ∀ i, L.weights i=1)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ) (htype : ∀ x y, B old x y → x=full ∧ y=full)
    (hC : (L.matrices old).PosSemidef) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction (L.domainRangeTargetProblem D B T old hC) base :=
  L.lemma33_domain_range_of_pathTyping hunit D B T old full hfull
    (pathDomainTyping_of_full_endpoints B old full htype) hC base available

/-- Specialized full/full-endpoint corollary for rational spectral powers. -/
def lemma33_domain_rationalPower (hunit : ∀ i, L.weights i=1)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ) (htype : ∀ x y, B old x y → x=full ∧ y=full)
    (hC : (L.matrices old).PosDef) (r : ℚ) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction (L.domainRationalPowerTargetProblem D B T old hC r) base :=
  L.lemma33_domain_rationalPower_of_pathTyping hunit D B T old full hfull
    (pathDomainTyping_of_full_endpoints B old full htype) hC r base available

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
