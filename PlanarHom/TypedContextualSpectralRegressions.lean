import PlanarHom.TypedContextualSpectralClosure

/-! Boundary regressions: unequal sides, zero and negative rational powers,
retained cross/XX/YY labels, ordinary unaries, and the empty-X transfer case. -/
noncomputable section
open Classical
open PlanarHom PlanarHom.Complexity PlanarHom.FiniteLanguageAliases
open PlanarHom.AlgebraicProductInterpolation PlanarHom.AlgebraicProductInterpolation.RealLanguage
open PlanarHom.TypedBipartiteSpectral PlanarHom.TypedBipartiteContext
open PlanarHom.EffectiveProductTransfer PlanarHom.SpectralProductZeros
namespace PlanarHom.TypedBipartiteContext.Regressions

private def policies : Fin 3→Fin 2→Fin 2→Prop := ![sameX,crossPolicy,sameY]

/-- The symbolic language retains all three kinds of companion and both
ordinary unary slots. The result is the original canonical source problem. -/
def inverseWithCompanions (L : RealLanguage (2+3) 3 2)
    (T : Fin 2→Fin 2→Prop) (hunit : ∀i,L.weights i=1)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : L.matrices 0=zeroExtendFin H)
    (hpd : H.PosDef) (ha : ∀i j,IsAlgebraic ℚ (H i j)) :=
  rationalPowerAppendReduction L policies T hunit 0 H hH rfl hpd (-1) ha

def zeroWithCompanions (L : RealLanguage (2+3) 3 2)
    (T : Fin 2→Fin 2→Prop) (hunit : ∀i,L.weights i=1)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : L.matrices 0=zeroExtendFin H)
    (hpd : H.PosDef) (ha : ∀i j,IsAlgebraic ℚ (H i j)) :=
  rationalPowerAppendReduction L policies T hunit 0 H hH rfl hpd 0 ha

example (F : Fin 3→Matrix (Fin (2+3)) (Fin (2+3)) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : H∈xFamily F policies) (hpd : H.PosDef) :
    cfc (fun z:ℝ=>z^((-1:ℚ):ℝ)) H∈xFamily F policies :=
  xFamily_rationalPower F policies H hH hpd (-1)

/-- Rational exponent zero produces the X identity and leaves Y zero. -/
example (H : Matrix (Fin 2) (Fin 2) ℝ) (hpd : H.PosDef) :
    zeroExtendFin (y:=3) (cfc (fun z:ℝ=>z^((0:ℚ):ℝ)) H)=
      zeroExtendFin (y:=3) (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  congr 1
  simpa only [Rat.cast_zero,Real.rpow_zero] using cfc_const_one ℝ H hpd.1

example : zeroExtendFin (y:=3) (1 : Matrix (Fin 2) (Fin 2) ℝ)≠1 := by
  intro h
  have he := congrArg (fun A : Matrix (Fin (2+3)) (Fin (2+3)) ℝ=>A (Fin.natAdd 2 0) (Fin.natAdd 2 0)) h
  norm_num [zeroExtendFin,Matrix.reindex_apply,zeroExtend,Matrix.fromBlocks] at he

/-- The private X-domain is not the whole ambient palette. -/
example : domains 2 3 0≠Set.univ := by
  intro h
  have hm : (Fin.natAdd 2 (0:Fin 3))∈domains 2 3 0 := by rw [h]; trivial
  obtain ⟨i,hi⟩ := hm
  have hv := congrArg Fin.val hi
  change i.val=2+0 at hv
  omega

/-- Concrete label policies survive ordinary binary appending. -/
example : appendOne policies sameX (Fin.castAdd 1 (1:Fin 3))=crossPolicy := by
  rw [appendOne_old]
  rfl
example : appendOne policies sameX (Fin.castAdd 1 (2:Fin 3))=sameY := by
  rw [appendOne_old]
  rfl

/-- Zero and negative ordinary unary labels are preserved literally. -/
example (L : RealLanguage (2+3) 3 2) (N : Matrix (Fin (2+3)) (Fin (2+3)) ℝ)
    (hN : ∀i j,IsAlgebraic ℚ (N i j)) (i : Fin (2+3))
    (hzero : L.unaries 0 i=0) (hnegative : L.unaries 1 i<0) :
    (L.appendBinary N hN).unaries 0 i=0 ∧ (L.appendBinary N hN).unaries 1 i<0 :=
  ⟨hzero,hnegative⟩

/-- Effective transfer returns to the same literal source with arbitrary U/T. -/
def effectiveWithCompanions (L : RealLanguage (2+3) 3 2)
    (T : Fin 2→Fin 2→Prop) (hunit : ∀i,L.weights i=1)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : L.matrices 0=zeroExtendFin H)
    (hpd : H.PosDef) (N : Matrix (Fin 2) (Fin 2) ℝ)
    (hN : ∀i j,IsAlgebraic ℚ (N i j)) (hNs : N.IsHermitian)
    (n₀ : ℕ) (hn₀ : 1≤n₀) (hp : ∀n,n₀≤n→∀i j,0<realPower H n i j)
    (hi : ProductIdentities (realPower H) N) :=
  TypedBipartiteContext.effectiveAppendReduction L policies T hunit 0 H hH rfl hpd
    N hN hNs 0 n₀ hn₀ hp hi

/-- No nonempty-side assumption leaks into the proved closure record. -/
example (F : Fin 3→Matrix (Fin (0+3)) (Fin (0+3)) ℝ) :
    ClosedMatrixFamily.EffectiveSpectralClosed (xFamily (x:=0) (y:=3) F policies) :=
  xFamily_effectiveClosed F policies

end PlanarHom.TypedBipartiteContext.Regressions
