import PlanarHom.TypedContextualSpectralBlocks

/-! Actual rational CFC closure of the X-only retained typed context.
The Sum-color spectral machine is joined to canonical Fin-color real languages
using proved equality of the raw prescribed-domain problems. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases
open TypedBipartiteSpectral SpectralFieldPresentation SpectralAvailability
variable {x y bt ut s : ℕ}

/-- Algebraicity of the literal rational CFC target, including zero and negative
rational exponents; positivity is needed only for the actual X block. -/
theorem rationalPower_algebraic (H : Matrix (Fin x) (Fin x) ℝ)
    (hH : ∀i j,IsAlgebraic ℚ (H i j)) (hpd : H.PosDef) (r : ℚ) :
    ∀i j,IsAlgebraic ℚ (cfc (fun z:ℝ=>z^(r:ℝ)) H i j) := by
  apply AlgebraicSpectralData.isAlgebraic_cfc_entry H hpd.1 hH
  intro z hz
  apply PositiveUnaryRationalPowers.isAlgebraic_real_rpow_rat _
    (AlgebraicSpectralData.isAlgebraic_of_mem_spectrum H hH hz) r
  obtain ⟨i,rfl⟩ := RealSpectralInterpolation.scalar_surjective H z hz
  exact RealSpectralInterpolation.scalar_pos H hpd i

/-- Genuine rational CFC append endpoint in the canonical field and answer
basis of the literal real language, with every old typed companion retained. -/
def rationalPowerAppendReduction (L : RealLanguage (x+y) bt ut)
    (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀i,L.weights i=1) (old : Fin bt)
    (H : Matrix (Fin x) (Fin x) ℝ) (hH : L.matrices old=zeroExtendFin H)
    (hB : B old=sameX) (hpd : H.PosDef) (r : ℚ)
    (ha : ∀i j,IsAlgebraic ℚ (H i j)) :
    PromisePolyTimeTuringReduction
      ((L.appendBinary (zeroExtendFin (cfc (fun z:ℝ=>z^(r:ℝ)) H))
        (zeroExtendFin_algebraic _ (rationalPower_algebraic H ha hpd r))).typedProblem
        (domains x y) (appendOne B sameX) T)
      (L.typedProblem (domains x y) B T) := by
  let C := sourceBlock L old
  have hC : realMatrix C=H := sourceBlock_real L old H hH
  have hpdC : (realMatrix C).PosDef := hC.symm ▸ hpd
  let f := fun z:ℝ=>z^(r:ℝ)
  let φ := inclusion C f
  let bF := SpectralFieldPresentation.basis C hpdC.1 f (powerFunction_algebraic C hpdC r)
  have p := L.typedAppendBinaryRealizationReduction (domains x y) B T sameX
    (zeroExtendFin (cfc f H)) (zeroExtendFin_algebraic _ (rationalPower_algebraic H ha hpd r))
    (SpectralFieldPresentation.field C f) bF
    (fun l i j=>φ (L.matricesK l i j)) (fun l i=>φ (L.unariesK l i))
    (fun i=>φ (L.weightsK i)) (zeroExtendFin (N C f))
    (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _=>rfl)
    (by
      intro i j
      rw [zeroExtendFin_coe]
      change zeroExtendFin (cfc f (realMatrix C)) i j=zeroExtendFin (cfc f H) i j
      rw [hC])
  have hw := weightsK_eq_one L hunit
  have available := typedRelabelReduction L L (domains x y) B B T T id id
    (by intros; assumption) (by intros; assumption)
    (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _=>rfl)
  have sourceEq := domainProblem_color_equiv L.basis
    (finSumFinEquiv : Fin x⊕Fin y≃Fin (x+y)) L.matricesK L.unariesK
    (fun _=>1) (domains x y) B T
  have availableSum : PromisePolyTimeTuringReduction
      (domainEvaluationProblem L.basis
        (fun l i j=>L.matricesK l (finSumFinEquiv i) (finSumFinEquiv j))
        (fun l i=>L.unariesK l (finSumFinEquiv i)) (fun _=>1)
        (fun d=>(finSumFinEquiv : Fin x⊕Fin y≃Fin (x+y)) ⁻¹' domains x y d) B T)
      (L.typedProblem (domains x y) B T) := by
    rw [sourceEq]
    simpa only [typedProblem,hw] using available
  have operation := typedRationalPowerAppend_joint L.basis
    (fun l i j=>L.matricesK l (finSumFinEquiv i) (finSumFinEquiv j))
    (fun l i=>L.unariesK l (finSumFinEquiv i))
    (fun d=>(finSumFinEquiv : Fin x⊕Fin y≃Fin (x+y)) ⁻¹' domains x y d) B T
    old 0 sumDomains_zero (sameX_path B old hB) (sum_sameX_type B old hB)
    C (fun _ _=>rfl) hpdC r (L.typedProblem (domains x y) B T) availableSum
  have targetEq := domainProblem_color_equiv bF
    (finSumFinEquiv : Fin x⊕Fin y≃Fin (x+y))
    (appendOne (fun l i j=>φ (L.matricesK l i j)) (zeroExtendFin (N C f)))
    (fun l i=>φ (L.unariesK l i)) (fun _=>1) (domains x y) (appendOne B sameX) T
  rw [appendZero_pullback] at targetEq
  rw [hB] at operation
  rw [targetEq] at operation
  simp only [hw,map_one] at p
  exact p.trans operation

/-- A temporary label for H is inserted, the genuine rational spectral machine
is used in that entire context, and the label is removed by contextual closure. -/
theorem xFamily_rationalPower (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop)
    (H : Matrix (Fin x) (Fin x) ℝ) (hH : H∈xFamily F FB) (hpd : H.PosDef) (r : ℚ) :
    cfc (fun z:ℝ=>z^(r:ℝ)) H∈xFamily F FB := by
  have ha := algebraic_of_zeroExtendFin H hH.2.algebraic
  refine ⟨cfc_predicate _ _,typed_contextual_operation (domains x y) F FB
    (fun _:Fin 1=>zeroExtendFin H) (fun _=>sameX) (fun _=>hH.2)
    (zeroExtendFin (cfc (fun z:ℝ=>z^(r:ℝ)) H)) sameX
    (zeroExtendFin_algebraic _ (rationalPower_algebraic H ha hpd r)) ?_⟩
  intro bt ut L B T hunit index hindex
  exact ⟨rationalPowerAppendReduction L B T hunit (index 0) H
    (hindex 0).1 (hindex 0).2 hpd r ha⟩

end PlanarHom.TypedBipartiteContext
