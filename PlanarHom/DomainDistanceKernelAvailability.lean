import PlanarHom.UniformDomainPowerSimulation
import PlanarHom.DistanceKernelRealAvailability
import PlanarHom.GlobalDomainSpectralAvailability

/-! Uniform rational distance-kernel availability on the exact prescribed-domain
promise. Canonical rational parameters accompany all successful raw graph words;
new path vertices receive explicit allowed full-domain metadata. -/
noncomputable section
open scoped Matrix.Norms.Operator
namespace PlanarHom.DomainDistanceKernelAvailability
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases EffectiveProductTransfer
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {dimension q bt ut dt : ℕ}

def targetProblem (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) : PromiseProblem :=
  RestrictedMatrixFamilyReduction.targetProblem basis BitEncoding.rat M (extendedUnaries U D) (fun _ => 1)
    (DistanceKernelEvaluationMachines.matrix (DistanceKernelAvailability.graph (M old)))
    (fun x : ℚ => 0 < x) (EncodedGraph (appendOne B (B old)) T)

omit [FiniteDimensional ℚ K] in
/-- Exact original domain-input promise, without a canonical-graph restriction. -/
theorem target_valid_iff (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (raw : Bits) :
    (targetProblem basis M U D B T old).valid raw ↔
      ∃ x : ℚ, ∃ rawGraph : Bits, raw = BitEncoding.frame (BitEncoding.rat.encode x) ++ rawGraph ∧
        0 < x ∧ EncodedInput (appendOne B (B old)) T rawGraph := by
  constructor
  · rintro ⟨⟨x,g⟩, hword, hx, hg⟩
    exact ⟨x,g.val,hword.symm,hx,(encodedInput_iff_graph _ T _).mpr
      ⟨g.value,g.decode_raw,hg⟩⟩
  · rintro ⟨x,rawGraph,hword,hx,hg⟩
    obtain ⟨g,hd,hg⟩ := (encodedInput_iff_graph _ T _).mp hg
    let gw : BitEncoding.ValidWord encoding := ⟨rawGraph,⟨g,hd⟩⟩
    refine ⟨(x,gw),hword.symm,hx,?_⟩
    have he : gw.value=g := BitEncoding.ValidWord.value_eq (w:=gw) hd
    change EncodedGraph (appendOne B (B old)) T gw.value
    rw [he]
    exact hg

/-- Arbitrary endpoint policies are supported exactly when the original C label
admits the necessary path endpoint/full-domain cases. -/
def reduction_of_pathTyping (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ)
    (hpath : ∀ x y, B old x y → PathDomainTyping B old full x y)
    (hH : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hconn : (DistanceKernelAvailability.graph (M old)).Connected)
    (hpositive : ∀ i j, (DistanceKernelAvailability.graph (M old)).Adj i j →
      0 < EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j) :
    PromisePolyTimeTuringReduction (targetProblem basis M U D B T old)
      (domainEvaluationProblem basis M U (fun _ => 1) D B T) := by
  let HT := EncodedGraph (appendOne B (B old)) T
  let target := DistanceKernelEvaluationMachines.matrix (K:=K) (DistanceKernelAvailability.graph (M old))
  have hidentity (x : ℚ) : ProductIdentities (matrixPowerRealFamily (M old))
      (fun i j => (target x i j : ℝ)) := by
    simpa only [target,DistanceKernelEvaluationMachines.matrix_real] using
      DistanceKernelProductIdentities.productIdentities (SpectralFieldPresentation.realMatrix (M old))
        hH hconn hpositive (x : ℝ)
  apply RestrictedMatrixFamilyReduction.reduction basis BitEncoding.rat M (extendedUnaries U D) (fun _ => 1)
    (fun n => M old ^ n) target (fun x : ℚ => 0<x) HT
    (fun _ h => (h.planarValid _ T).1) (fun _ h s => h.parallelLabel _ T bt s)
    1 (by omega)
    (spectralCandidateCount q (Nat.card (spectrum ℝ (SpectralFieldPresentation.realMatrix (M old)))))
  · exact SpectralPowerEvaluationMachines.fp_matrixPowers basis (M old) hH.1
  · exact DistanceKernelEvaluationMachines.fp_matrix basis _
  · intro n hn i j hz
    have hp := MatrixLogCoefficients.exp_positive_time_entry_pos
      (EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)))
      (cfc_predicate Real.log _) hconn hpositive (n : ℝ) (by exact_mod_cast (Nat.zero_lt_of_lt hn)) i j
    rw [← SpectralProductZeros.realPower_eq_exp_smul_log _ hH] at hp
    change 0 < matrixPowerRealFamily (M old) n i j at hp
    rw [← matrixPowerFamily_coe _ hH.1, hz] at hp
    exact lt_irrefl 0 hp
  · intro x _
    exact spectral_samples (M old) (target x) hH 1
      (DistanceKernelEvaluationMachines.matrix_symm _ _) (hidentity x)
  · exact UniformDomainPowerSimulation.reduction basis M U D B T old full hfull hpath

/-- Canonical source interpretation: C is already global on the ambient color
set, and original narrower vertex domains and every companion policy are retained. -/
def reduction_global (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ)
    (hH : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hconn : (DistanceKernelAvailability.graph (M old)).Connected)
    (hpositive : ∀ i j, (DistanceKernelAvailability.graph (M old)).Adj i j →
      0 < EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j) :
    PromisePolyTimeTuringReduction (targetProblem basis M U D (withGlobalMatrix B old) T old)
      (domainEvaluationProblem basis M U (fun _ => 1) D (withGlobalMatrix B old) T) :=
  reduction_of_pathTyping basis M U D (withGlobalMatrix B old) T old full hfull
    (fun x y _ => withGlobalMatrix_pathTyping B old full x y) hH hconn hpositive

end PlanarHom.DomainDistanceKernelAvailability
