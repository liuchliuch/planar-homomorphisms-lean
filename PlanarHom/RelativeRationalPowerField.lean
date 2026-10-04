import PlanarHom.RelativeWeightedSpectralField
import PlanarHom.DiagonalRationalPowerCompatibility

/-! NEW actual positive rational-power constants in a finite algebraic extension
of an arbitrary real source field. All roots are fixed data with their literal
Real.rpow values, and satisfy a proved positive-degree power equation. -/
noncomputable section
namespace PlanarHom.RelativeRationalPowerField
open PositiveUnaryRationalPowers RelativeWeightedSpectralField
variable {F:Type} [Field F] [Algebra F ℝ] {q s:ℕ}

theorem algebraic_zpow {x:ℝ} (hx:IsAlgebraic F x) (z:ℤ) : IsAlgebraic F (x^z) := by
  cases z with
  | ofNat z=>simpa using hx.pow z
  | negSucc z=>simpa only [zpow_negSucc] using (hx.pow (z+1)).inv

theorem algebraic_rpow {x:ℝ} (hx:0<x) (ha:IsAlgebraic F x) (r:ℚ) :
    IsAlgebraic F (x^(r:ℝ)) := by
  apply IsAlgebraic.of_pow r.den_pos
  rw [real_rpow_rat_den x hx r]
  exact algebraic_zpow ha r.num

def constants (w:Fin q→F) (r:Fin s→ℚ) : Fin s×Fin q→ℝ :=
  fun p=>realWeights w p.2^(r p.1:ℝ)
def field (w:Fin q→F) (r:Fin s→ℚ) : IntermediateField F ℝ :=
  IntermediateField.adjoin F (Set.range (constants w r))

theorem finiteDimensional (w:Fin q→F) (hw:∀i,0<realWeights w i) (r:Fin s→ℚ) :
    FiniteDimensional F (field w r) := by
  apply IntermediateField.finiteDimensional_adjoin
  rintro _ ⟨⟨j,i⟩,rfl⟩
  exact (algebraic_rpow (hw i) (isAlgebraic_algebraMap (w i)) (r j)).isIntegral

def powered (w:Fin q→F) (r:Fin s→ℚ) (j:Fin s) (i:Fin q) : field w r :=
  ⟨constants w r (j,i),IntermediateField.subset_adjoin F _ (Set.mem_range_self (j,i))⟩

@[simp] theorem powered_real (w:Fin q→F) (r:Fin s→ℚ) (j:Fin s) (i:Fin q) :
    (powered w r j i:ℝ)=realWeights w i^(r j:ℝ) := rfl

end PlanarHom.RelativeRationalPowerField
