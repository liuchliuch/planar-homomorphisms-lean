import PlanarHom.RectangularCommonChartNoise
noncomputable section
open Classical
namespace PlanarHom.RectangularChartTransport
open ClosedMatrixFamily RectangularMixedGadgets RectangularWalshConvolution
variable {x y : ℕ} [Nonempty (Fin x)] [Nonempty (Fin y)]
variable {SX : Set (Matrix (Fin x) (Fin x) ℝ)} {SY : Set (Matrix (Fin y) (Fin y) ℝ)}
theorem tensor_form_from_common_charts
    (WX : CommonCubeChart SX) (WY : CommonCubeChart SY)
    (hAX : AlgebraicSourceClosed SX) (hAY : AlgebraicSourceClosed SY)
    (hEX : EffectiveSpectralClosed SX) (hEY : EffectiveSpectralClosed SY)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀ i j,0<B i j)
    (h k : ℕ) (hh : h≠0) (hk : k≠0)
    (hseedX : ∃ γ : ℝ,∃ ρ : Fin WX.dimension→ℝ,(∀ i,0<ρ i ∧ ρ i<1) ∧
      Matrix.reindex WX.graphIso.toEquiv WX.graphIso.toEquiv (fun i j=>(B*B.transpose) i j^h)=γ • Boolean.tensor ρ)
    (hseedY : ∃ γ : ℝ,∃ ρ : Fin WY.dimension→ℝ,(∀ i,0<ρ i ∧ ρ i<1) ∧
      Matrix.reindex WY.graphIso.toEquiv WY.graphIso.toEquiv (fun i j=>(B.transpose*B) i j^k)=γ • Boolean.tensor ρ)
    (hclass : ∀ N∈SX,(∀ i j,0<N i j) → ∃ γ : ℝ,∃ ρ : Fin WX.dimension→ℝ,
      0<γ ∧ (∀ i,0<ρ i) ∧ Matrix.reindex WX.graphIso.toEquiv WX.graphIso.toEquiv N=γ • Boolean.tensor ρ)
    (hthree : ∀ K∈SY,B*K*B.transpose∈SX)
    (hdiamond : ∀ K∈SX,entrySquare (K*B)*(entrySquare (K*B)).transpose∈SX) :
    ∃ d : ℕ,∃ eX : Fin x≃Boolean.Cube d,∃ eY : Fin y≃Boolean.Cube d,
      ∃ γ : ℝ,∃ ρ : Fin d→ℝ,0<γ ∧ (∀ i,0<ρ i ∧ ρ i<1) ∧
      ∀ i j,B i j=γ*Boolean.tensor ρ (eX i) (eY j) := by
  let eX := WX.graphIso.toEquiv
  let eY := WY.graphIso.toEquiv
  let B' := Matrix.reindex eX eY B
  obtain ⟨γX,ρX,hρX,hX⟩ := hseedX
  obtain ⟨γY,ρY,hρY,hY⟩ := hseedY
  have hXp : ∀ i j,(B'*B'.transpose) i j^h=γX*Boolean.tensor ρX i j := by
    have hm : B'*B'.transpose=Matrix.reindex eX eX (B*B.transpose) := by
      rw [reindex_mul eX eY eX,reindex_transpose]
    intro i j
    rw [hm]
    exact congrFun (congrFun hX i) j
  have hYp : ∀ i j,(B'.transpose*B') i j^k=γY*Boolean.tensor ρY i j := by
    have hm : B'.transpose*B'=Matrix.reindex eY eY (B.transpose*B) := by
      rw [reindex_mul eY eX eY,reindex_transpose]
    intro i j
    rw [hm]
    exact congrFun (congrFun hY i) j
  obtain ⟨hmix,hforms⟩ := noise_forms_from_common_charts WX WY hAX hAY hEX hEY B hB hclass hthree hdiamond
  obtain ⟨γ,ρ,_,hρ,hg⟩ := hmix (1/2) (by norm_num) (by norm_num)
  have hpB : ∀ i j,0<B' i j := fun i j=>hB (eX.symm i) (eY.symm j)
  obtain ⟨hd,f,c,σ,hc,hσ,hform⟩ := rectangular_tensor_of_physical_forms B' hpB
    h k hh hk γX γY ρX ρY hρX hρY hXp hYp (1/2) (by norm_num) (by norm_num)
    γ ρ (fun i=>ne_of_gt (by linarith [hρ i]))
    (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hg)
    (fun t ht ht1=>by obtain ⟨a,r,_,hr,he⟩ := hforms t ht ht1; exact ⟨a,r,hr,he⟩)
  refine ⟨WX.dimension,eX,eY.trans f,c,σ,hc,hσ,?_⟩
  intro i j
  simpa only [B',Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Equiv.trans_apply] using hform (eX i) (eY j)
end PlanarHom.RectangularChartTransport
