import PlanarHom.RectangularCommonChartForms
import PlanarHom.RectangularNoiseTensorScaling
noncomputable section
open Classical
namespace PlanarHom.RectangularChartTransport
open ClosedMatrixFamily RectangularMixedGadgets
open RectangularWalshConvolution
variable {x y : ℕ} [Nonempty (Fin x)] [Nonempty (Fin y)]
variable {SX : Set (Matrix (Fin x) (Fin x) ℝ)} {SY : Set (Matrix (Fin y) (Fin y) ℝ)}
theorem noise_forms_from_common_charts
    (WX : CommonCubeChart SX) (WY : CommonCubeChart SY)
    (hAX : AlgebraicSourceClosed SX) (hAY : AlgebraicSourceClosed SY)
    (hEX : EffectiveSpectralClosed SX) (hEY : EffectiveSpectralClosed SY)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀ i j,0<B i j)
    (hclass : ∀ N∈SX,(∀ i j,0<N i j) → ∃ γ : ℝ,∃ ρ : Fin WX.dimension→ℝ,
      0<γ ∧ (∀ i,0<ρ i) ∧ Matrix.reindex WX.graphIso.toEquiv WX.graphIso.toEquiv N=γ • Boolean.tensor ρ)
    (hthree : ∀ K∈SY,B*K*B.transpose∈SX)
    (hdiamond : ∀ K∈SX,entrySquare (K*B)*(entrySquare (K*B)).transpose∈SX) :
    (∀ t : ℚ,0<t → t<1 → ∃ γ : ℝ,∃ ρ : Fin WX.dimension→ℝ,
      0<γ ∧ (∀ i,0<ρ i) ∧
      (Matrix.reindex WX.graphIso.toEquiv WY.graphIso.toEquiv B)*noiseMatrix (t:ℝ)*
      (Matrix.reindex WX.graphIso.toEquiv WY.graphIso.toEquiv B).transpose=γ • Boolean.tensor ρ) ∧
    (∀ t : ℚ,0<t → t<1 → ∃ γ : ℝ,∃ ρ : Fin WX.dimension→ℝ,
      0<γ ∧ (∀ i,0<ρ i) ∧ parallelSquareGram
      (Matrix.reindex WX.graphIso.toEquiv WY.graphIso.toEquiv B) (t:ℝ)=γ • Boolean.tensor ρ) := by
  let eX := WX.graphIso.toEquiv
  let eY := WY.graphIso.toEquiv
  let B' := Matrix.reindex eX eY B
  constructor
  · intro t ht ht1
    let p := rationalNoiseTensorParameter t
    have hp : 0<p := (rationalNoiseTensorParameter_range ht ht1).1
    let K := WY.kernel p
    have hK := WY.kernel_mem hAY hEY p
    obtain ⟨γ,ρ,hγ,hρ,he⟩ := hclass (B*K*B.transpose) (hthree K hK)
      (three_positive B hB K (WY.kernel_positive p hp))
    refine ⟨noiseTensorScale WY.dimension (t:ℝ)*γ,ρ,
      mul_pos (noiseTensorScale_pos _ (by exact_mod_cast ht)) hγ,hρ,?_⟩
    have hr : Matrix.reindex eY eY K=tensorMatrix (fun _:Fin WY.dimension=>noiseTensorParameter (t:ℝ)) := by
      simpa only [K,eY,p,rationalNoiseTensorParameter_cast,tensorMatrix] using WY.reindex_kernel p
    have hh : B'*tensorMatrix (fun _:Fin WY.dimension=>noiseTensorParameter (t:ℝ))*B'.transpose=
        γ • Boolean.tensor ρ := by
      rw [←hr,←reindex_three eX eY B K]
      exact he
    rw [mixed_noise_eq_scaled_tensor _ (by exact_mod_cast ht),hh,smul_smul]
  · intro t ht ht1
    let p := rationalNoiseTensorParameter t
    have hp : 0<p := (rationalNoiseTensorParameter_range ht ht1).1
    let K := WX.kernel p
    have hK := WX.kernel_mem hAX hEX p
    obtain ⟨γ,ρ,hγ,hρ,he⟩ := hclass (entrySquare (K*B)*(entrySquare (K*B)).transpose)
      (hdiamond K hK) (diamond_positive B hB K (WX.kernel_positive p hp))
    refine ⟨noiseTensorScale WX.dimension (t:ℝ)^4*γ,ρ,
      mul_pos (pow_pos (noiseTensorScale_pos _ (by exact_mod_cast ht)) 4) hγ,hρ,?_⟩
    have hr : Matrix.reindex eX eX K=Boolean.tensor (fun _:Fin WX.dimension=>noiseTensorParameter (t:ℝ)) := by
      simpa only [K,eX,p,rationalNoiseTensorParameter_cast] using WX.reindex_kernel p
    have hh : kernelParallelSquareGram
        (Boolean.tensor (fun _:Fin WX.dimension=>noiseTensorParameter (t:ℝ))) B'=
        γ • Boolean.tensor ρ := by
      rw [←hr]
      change entrySquare (Matrix.reindex eX eX K*B')*(entrySquare (Matrix.reindex eX eX K*B')).transpose=_
      rw [←reindex_diamond eX eY B K]
      exact he
    rw [parallelSquareGram_eq_scaled_tensorGram _ (by exact_mod_cast ht),hh,smul_smul]
end PlanarHom.RectangularChartTransport
