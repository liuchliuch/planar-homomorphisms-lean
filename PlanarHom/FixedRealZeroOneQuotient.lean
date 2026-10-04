import PlanarHom.FixedRealTwinReduction

/-! NEW removal of positive real weights from the actual nonzero twin quotient
of a zero-one source. Its retained rows are proved nonzero and nonproportional;
these are not extra hypotheses of support hardness. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealTwins
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open ActualTwins FixedRealComponents RelativeWeightedSpectralField
variable {n e:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K) (φ:K→+*ℝ)

theorem reduced_image_rows_ne_zero (A:Matrix C C K) (hs:∀i j,A i j=A j i)
    (i:Fin (reducedCount A hs)) : (fun j=>φ (reducedMatrix A hs i j))≠0 := by
  intro h
  apply reducedMatrix_rows_ne_zero A hs i
  funext j
  apply φ.injective
  simpa only [Pi.zero_apply,map_zero] using congrFun h j

theorem reduced_image_rows_injective (A:Matrix C C K) (hs:∀i j,A i j=A j i) :
    Function.Injective (fun i j=>φ (reducedMatrix A hs i j)) := by
  intro i j h
  apply reducedMatrix_rows_injective A hs
  funext k
  exact φ.injective (congrFun h k)

def zeroOneReduction (A:Matrix C C K) (hs:∀i j,A i j=A j i)
    (w:C→K) (hw:∀i,0<φ (w i)) (h01:∀i j,A i j=0 ∨ A i j=1) :
    Reduction (problem basis (fun _:Fin 1=>reducedMatrix A hs) (fun i:Fin 0=>i.elim0) (fun _=>1))
      (problem basis (fun _:Fin 1=>A) (fun i:Fin 0=>i.elim0) w) := by
  letI : LinearOrder K := LinearOrder.lift' φ φ.injective
  letI : IsStrictOrderedRing K := Function.Injective.isStrictOrderedRing φ
    φ.map_zero φ.map_one φ.map_add φ.map_mul (fun {_ _}=>Iff.rfl) (fun {_ _}=>Iff.rfl)
  letI : DecidableEq K := Classical.decEq K
  letI : Algebra K ℝ := φ.toAlgebra
  have hwK:∀i,0<w i := by
    intro i
    change φ 0<φ (w i)
    simpa only [map_zero] using hw i
  have hsymm:∀i j,realMatrix (reducedMatrix A hs) i j=realMatrix (reducedMatrix A hs) j i:=
    fun i j=>congrArg φ (reducedMatrix_symmetric A hs i j)
  have hweight:∀i,0<realWeights (reducedWeight A hs w) i := by
    intro i
    change 0<φ (reducedWeight A hs w i)
    rw [reducedWeight_eq_sum_rows,map_sum]
    apply Finset.sum_pos
    · intro c _;exact hw c.val
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨representative A hs i,rfl⟩⟩
  have hz:∀i j,realMatrix (reducedMatrix A hs) i j=0 ∨ realMatrix (reducedMatrix A hs) i j=1 := by
    intro i j
    have h:=Twins.quotientMatrix_zeroOne A hs h01 (reducedIndex A hs i).val (reducedIndex A hs j).val
    rcases h with h|h
    · exact Or.inl (by simpa only [map_zero] using congrArg φ h)
    · exact Or.inr (by simpa only [map_one] using congrArg φ h)
  have hproj:=Twins.zeroOne_rows_nonproportional (realMatrix (reducedMatrix A hs)) hz
    (reduced_image_rows_ne_zero φ A hs) (reduced_image_rows_injective φ A hs)
  exact (FixedRealWeightRemoval.removePositiveWeights basis (fun _:Fin 1=>reducedMatrix A hs)
    (fun i:Fin 0=>i.elim0) (reducedWeight A hs w) 0 hsymm hweight
    (reduced_image_rows_ne_zero φ A hs) hproj).trans (weightedReducedReduction basis A hs w hwK)

end PlanarHom.FixedRealTwins
