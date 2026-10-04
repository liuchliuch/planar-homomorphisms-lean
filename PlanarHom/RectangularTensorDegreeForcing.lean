import PlanarHom.RectangularOrthogonalDegrees
import PlanarHom.RectangularBooleanSubsets

/-! NEW cancellation step forcing genuine Fourier degrees. Positive tensor
weights cancel from the mixed-noise eigenvalue identity, and no distinctness
among the individual coordinate weights is required. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

theorem weighted_degree_additive (z:ℝ) (hz:0<z) (hz1:z<1)
    (w:Cube d→ℝ) (hw:∀S,0<w S) (h:Cube d→ℕ)
    (hw0:w (fun _=>false)=1) (hh0:h (fun _=>false)=0)
    (hwprod:∀S,w S=∏i∈bitSupport S,w (unitBit i))
    (hmix:∀S,(w S*z^(h S))*(w (fun _=>false)*z^(h (fun _=>false)))^(Boolean.degree S)=
      (w (fun _=>false)*z^(h (fun _=>false)))*
        (∏i∈bitSupport S,w (unitBit i)*z^(h (unitBit i)))) :
    ∀S,h S=∑i∈bitSupport S,h (unitBit i):=by
  intro S
  have he:=hmix S
  simp only [hw0,hh0,pow_zero,mul_one,one_pow,one_mul] at he
  rw [Finset.prod_mul_distrib,←hwprod S,Finset.prod_pow_eq_pow_sum] at he
  exact pow_right_injective₀ hz hz1.ne ((mul_left_cancel₀ (hw S).ne') he)

theorem weighted_degree_preserved (z:ℝ) (hz:0<z) (hz1:z<1)
    (w:Cube d→ℝ) (hw:∀S,0<w S) (h:Cube d→ℕ)
    (hw0:w (fun _=>false)=1) (hh0:h (fun _=>false)=0)
    (hwprod:∀S,w S=∏i∈bitSupport S,w (unitBit i))
    (hmix:∀S,(w S*z^(h S))*(w (fun _=>false)*z^(h (fun _=>false)))^(Boolean.degree S)=
      (w (fun _=>false)*z^(h (fun _=>false)))*
        (∏i∈bitSupport S,w (unitBit i)*z^(h (unitBit i))))
    (hbound:∀S,h S≤d) (hpositive:∀i,1≤h (unitBit i)) : h=Boolean.degree:=by
  apply additive_degree_is_card h _ hbound hpositive
  intro S
  rw [weighted_degree_additive z hz hz1 w hw h hw0 hh0 hwprod hmix S]
  simp [bitSupport,Finset.sum_filter]

theorem normalized_degree_zero_and_singletons
    (O:Matrix (Cube d) (Cube d) ℝ) (hO:O*O.transpose=1)
    (h00:O (fun _=>false) (fun _=>false)=1)
    (hcol:∀S,S≠(fun _=>false)→O S (fun _=>false)=0)
    (h:Cube d→ℕ) (hsupport:∀S T,O S T≠0→Boolean.degree T=h S) :
    h (fun _=>false)=0 ∧ ∀i,1≤h (unitBit i):=by
  constructor
  · have hz:=hsupport (fun _=>false) (fun _=>false) (by rw [h00];norm_num)
    simpa [Boolean.degree] using hz.symm
  · intro i
    obtain ⟨T,hT⟩:=orthogonal_row_nonzero O hO (unitBit i)
    have he:=hsupport (unitBit i) T hT
    by_contra hi
    have hz:h (unitBit i)=0:=by omega
    have hT0:T=(fun _=>false):=(degree_zero_iff T).mp (he.trans hz)
    subst T
    apply hT
    apply hcol
    intro hs
    have hv:=congrFun hs i
    simp [unitBit] at hv

end PlanarHom.RectangularWalshConvolution
