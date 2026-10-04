import PlanarHom.FixedRealBipartiteLeftHard

/-! The right-side hard reduction is the left-side reduction after an actual
fixed color swap. The two weight vectors are swapped, never identified. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealBipartiteLeftHard
open DensePolynomial Complexity RepresentedBit PositiveRealCore
variable {n e:ℕ} {F I:Type} [Field F] [Algebra (RationalFunction n) F] [Algebra F ℝ]
  [Fintype I] [DecidableEq I]

def swapReduction (basis:Module.Basis (Fin e) (RationalFunction n) F) (B:Matrix I I F) (μ ν:I→F) :
    Reduction (problem basis B.transpose ν μ) (problem basis B μ ν) := by
  have hh:=FixedRealColorReduction.homogeneous basis (Equiv.sumComm I I) (double B) (Sum.elim μ ν)
  have hm:(fun i j=>double B ((Equiv.sumComm I I) i) ((Equiv.sumComm I I) j))=double B.transpose := by
    funext i j; cases i <;> cases j <;> rfl
  have hw:(fun i=>Sum.elim μ ν ((Equiv.sumComm I I) i))=Sum.elim ν μ := by
    funext i; cases i <;> rfl
  have hmf:(fun (_:Fin 1) i j=>double B ((Equiv.sumComm I I) i) ((Equiv.sumComm I I) j))=
      (fun _:Fin 1=>double B.transpose) := funext (fun _=>hm)
  rw [hmf,hw] at hh
  exact hh

theorem transpose_leftGram (B:Matrix I I F) (μ ν:I→F) :
    leftGram (realB B.transpose) (realW ν) (realW μ)=rightGram (realB B) (realW μ) (realW ν) := by
  have he:decorated (realB B.transpose) (realW ν) (realW μ)=
      (decorated (realB B) (realW μ) (realW ν)).transpose := by
    ext i j
    simp only [decorated_entry,Matrix.transpose_apply,realB]
    ring
  rw [leftGram,he,Matrix.transpose_transpose,rightGram]

theorem right_hard (basis:Module.Basis (Fin e) (RationalFunction n) F)
    (B:Matrix I I F) (μ ν:I→F) (hμ:∀i,0<realW μ i) (hν:∀i,0<realW ν i)
    (hB:IsUnit (realB B))
    (hpd:(rightGram (realB B) (realW μ) (realW ν)).PosDef)
    (hp:∀i j,0<rightGram (realB B) (realW μ) (realW ν) i j)
    (hnon:∃i j,rightGram (realB B) (realW μ) (realW ν) i i≠rightGram (realB B) (realW μ) (realW ν) j j) :
    SharpPHard (problem basis B μ ν) := by
  have hBT:IsUnit (realB B.transpose):=(Matrix.isUnit_transpose (realB B)).mpr hB
  have hh:=left_hard basis B.transpose ν μ hν hμ hBT
    (by rw [transpose_leftGram]; exact hpd)
    (by intro i j; rw [transpose_leftGram]; exact hp i j)
    (by rw [transpose_leftGram]; exact hnon)
  exact hh.trans (swapReduction basis B μ ν)

end PlanarHom.FixedRealBipartiteLeftHard
