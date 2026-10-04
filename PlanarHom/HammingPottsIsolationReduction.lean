import PlanarHom.HammingPottsFieldFamily

/-! NEW actual source program isolating every occurrence of a chosen clique
size in a maximum Hamming graph. All original labels and unaries coexist. -/
noncomputable section
namespace PlanarHom.HammingPottsIsolationReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases EffectiveProductTransfer
open HammingPottsProductIdentities HammingPottsFieldFamily CartesianGeometry
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {q d bt ut dimension : ℕ}

/-- The selected Potts tensor is simulated by a genuine polynomial-time oracle
machine. Squared-kernel source queries and exact product identities are proved,
not supplied as availability or interpolation premises. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hG : (DistanceKernelAvailability.graph (M old)).Connected)
    (hedge : ∀ i j, (DistanceKernelAvailability.graph (M old)).Adj i j →
      0 < EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j)
    (sizes : Fin d → ℕ) (hsizes : ∀ r, 2 ≤ sizes r)
    (e : DistanceKernelAvailability.graph (M old) ≃g hammingGraph (fun r=>Fin (sizes r)))
    (s : ℕ) (hs : 2 ≤ s) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (targetK sizes s e.toEquiv)) U (fun _=>1))
      (evaluationProblem basis M U (fun _=>1)) := by
  have hfamily : polynomialFamily (family (K:=K) sizes e.toEquiv) =
      (fun n : ℕ=>DistanceKernelEvaluationMachines.matrix (K:=K) (DistanceKernelAvailability.graph (M old))
        (n:ℚ)^2) := by
    funext n
    exact family_nat_value sizes _ e n
  have source := DistanceKernelAvailability.uniformSquareReduction basis M U old hA hG hedge
  rw [←hfamily] at source
  apply polynomial_reduction basis M U (family sizes e.toEquiv) (targetK sizes s e.toEquiv)
    (2*d) 1 (by decide) (family_degree sizes e.toEquiv) ?_ ?_ ?_ ?_
    (evaluationProblem basis M U (fun _=>1)) source
  · intro t i j
    rw [realFamily_eq,realFamily_eq]
    exact squareFamily_symmetric sizes t (e i) (e j)
  · intro i j
    apply K.val.injective
    change (targetK (K:=K) sizes s e.toEquiv i j:ℝ) =
      (targetK (K:=K) sizes s e.toEquiv j i:ℝ)
    rw [targetK_real,targetK_real]
    exact target_symmetric sizes s (e i) (e j)
  · intro n hn i j
    rw [realFamily_eq]
    apply squareFamily_positive sizes hsizes
    exact_mod_cast (show 0<n by omega)
  · have hreal : polynomialRealFamily (family (K:=K) sizes e.toEquiv) =
        (fun t i j => squareFamily sizes t (e i) (e j)) := by
      funext t i j
      exact realFamily_eq sizes e.toEquiv t i j
    have htarget : (fun i j=>(targetK (K:=K) sizes s e.toEquiv i j:ℝ)) =
        (fun i j=>target sizes s (e i) (e j)) := by
      funext i j
      exact targetK_real sizes s e.toEquiv i j
    rw [hreal,htarget]
    exact productIdentities sizes hsizes hs e.toEquiv

end PlanarHom.HammingPottsIsolationReduction
