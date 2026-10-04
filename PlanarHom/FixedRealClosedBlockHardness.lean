import PlanarHom.FixedRealColorReduction
import PlanarHom.FixedRealSupportRestriction
import PlanarHom.FixedRealPositiveDiagonalHardness
import Mathlib.Algebra.Order.Ring.InjSurj

/-! Actual hardness transfer from one closed positive PD color block. The
induced real order is used only in the finite rooted-signature proof, never as
an algorithmic sign oracle. Original answer representations are preserved. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealClosedBlockHardness
open DensePolynomial Complexity RepresentedBit
variable {n e q:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

def block (M:Matrix (Fin q) (Fin q) K) (X:Set (Fin q)) :
    Matrix (Fin (Fintype.card X)) (Fin (Fintype.card X)) K :=
  fun i j=>M ((Fintype.equivFin X).symm i).val ((Fintype.equivFin X).symm j).val

theorem source_hard (basis:Module.Basis (Fin e) (RationalFunction n) K) (φ:K→+*ℝ)
    (M:Matrix (Fin q) (Fin q) K) (hs:∀i j,M i j=M j i) (X:Set (Fin q))
    (hX:RootedRestriction.ColorClosed M X)
    (hpd:(show Matrix (Fin (Fintype.card X)) (Fin (Fintype.card X)) ℝ from fun i j=>φ (block M X i j)).PosDef)
    (hp:∀i j,0<φ (block M X i j)) (hnon:∃i j,block M X i i≠block M X j j) :
    SharpPHard (FixedRealMixedInterpolation.problem basis (fun _:Fin 1=>M) (fun l:Fin 0=>l.elim0) (fun _=>1)) := by
  letI : LinearOrder K := LinearOrder.lift' φ φ.injective
  letI : IsStrictOrderedRing K := Function.Injective.isStrictOrderedRing φ φ.map_zero φ.map_one
    φ.map_add φ.map_mul (fun {_ _}=>Iff.rfl) (fun {_ _}=>Iff.rfl)
  have hh:=FixedRealApproximation.positive_nonconstant_diagonal_hard basis φ (block M X) hpd hp hnon
  have hc:=FixedRealColorReduction.homogeneous basis (Fintype.equivFin X).symm
    (fun i j:X=>M i.val j.val) (fun _=>1)
  have hr:=FixedRealRootRestriction.submatrixReduction basis M hs (fun _=>1) (fun _=>zero_lt_one) X hX
  exact hh.trans (hc.trans hr)

end PlanarHom.FixedRealClosedBlockHardness
