import PlanarHom.TypedContextualSpectralBlocks

/-! Canonical-real-language effective spectral transfer on the actual X block.
All old binary companions, ordinary unary labels and their original endpoint
policies survive the operation and its field conversion unchanged. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases
open TypedBipartiteSpectral SpectralFieldPresentation EffectiveProductTransfer
open SymmetricProductIdentities SpectralProductZeros
variable {x y bt ut s : ℕ}

/-- Actual canonical appended-language endpoint for effective Lemma 3.10(S).
Only X-entry positivity and X product identities are assumed. -/
def effectiveAppendReduction (L : RealLanguage (x+y) bt ut)
    (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀i,L.weights i=1) (old : Fin bt)
    (H : Matrix (Fin x) (Fin x) ℝ) (hH : L.matrices old=zeroExtendFin H)
    (hB : B old=sameX) (hpd : H.PosDef)
    (N : Matrix (Fin x) (Fin x) ℝ) (hN : ∀i j,IsAlgebraic ℚ (N i j))
    (hNs : N.IsHermitian) (x₀ : Fin x) (n₀ : ℕ) (hn₀ : 1≤n₀)
    (hp : ∀n,n₀≤n→∀i j,0<realPower H n i j)
    (hi : ProductIdentities (realPower H) N) :
    PromisePolyTimeTuringReduction
      ((L.appendBinary (zeroExtendFin N) (zeroExtendFin_algebraic N hN)).typedProblem
        (domains x y) (appendOne B sameX) T)
      (L.typedProblem (domains x y) B T) := by
  let C := sourceBlock L old
  have hC : realMatrix C=H := sourceBlock_real L old H hH
  have hpdC : (realMatrix C).PosDef := hC.symm ▸ hpd
  let entries := fun p : Fin x×Fin x=>N p.1 p.2
  let φ := sourceInclusion L.field entries
  have p := L.typedAppendBinaryRealizationReduction (domains x y) B T sameX
    (zeroExtendFin N) (zeroExtendFin_algebraic N hN)
    (extensionField L.field entries) (extensionBasis L.field entries (fun p=>hN p.1 p.2))
    (fun l i j=>φ (L.matricesK l i j)) (fun l i=>φ (L.unariesK l i))
    (fun i=>φ (L.weightsK i)) (zeroExtendFin (fun i j=>targetValue L.field entries (i,j)))
    (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _=>rfl)
    (fun i j=>zeroExtendFin_coe _ i j)
  have available := typedRelabelReduction L L (domains x y) B B T T id id
    (by intros; assumption) (by intros; assumption)
    (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _=>rfl)
  have hw := weightsK_eq_one L hunit
  have availableUnit : PromisePolyTimeTuringReduction
      (domainEvaluationProblem L.basis L.matricesK L.unariesK (fun _=>1) (domains x y) B T)
      (L.typedProblem (domains x y) B T) := by
    simpa only [typedProblem,hw] using available
  have r := typedEffectiveOverfield_joint L.basis L.matricesK L.unariesK (domains x y) B T
    old 0 domains_zero (sameX_path B old hB) (sameX_type B old hB) C (fun _ _=>rfl)
    N hN x₀ hpdC hNs n₀ hn₀
    (by simpa only [matrixPowerRealFamily,hC] using hp)
    (by
      change ProductIdentities (realPower (realMatrix C)) N
      rw [hC]
      exact hi)
    (L.typedProblem (domains x y) B T) availableUnit
  simp only [hw,map_one] at p
  rw [hB] at r
  exact p.trans r

/-- Effective transfer closes the contextual X-family by temporarily adding H,
using the actual typed spectral machine, and eliminating that added label. -/
theorem xFamily_effective (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop)
    (H : Matrix (Fin x) (Fin x) ℝ) (hH : H∈xFamily F FB) (hpd : H.PosDef)
    (N : Matrix (Fin x) (Fin x) ℝ) (hN : ∀i j,IsAlgebraic ℚ (N i j))
    (hNs : N.IsHermitian) (x₀ : Fin x) (n₀ : ℕ) (hn₀ : 1≤n₀)
    (hp : ∀n,n₀≤n→∀i j,0<realPower H n i j)
    (hi : ProductIdentities (realPower H) N) : N∈xFamily F FB := by
  refine ⟨hNs,typed_contextual_operation (domains x y) F FB
    (fun _:Fin 1=>zeroExtendFin H) (fun _=>sameX) (fun _=>hH.2)
    (zeroExtendFin N) sameX (zeroExtendFin_algebraic N hN) ?_⟩
  intro bt ut L B T hunit index hindex
  exact ⟨effectiveAppendReduction L B T hunit (index 0) H (hindex 0).1 (hindex 0).2
    hpd N hN hNs x₀ n₀ hn₀ hp hi⟩

end PlanarHom.TypedBipartiteContext
