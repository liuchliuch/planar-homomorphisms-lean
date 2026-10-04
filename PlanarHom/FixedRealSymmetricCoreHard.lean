import PlanarHom.FixedRealSquareRootGramSource
import PlanarHom.FixedRealCoreObstructions
import PlanarHom.FixedRealPositiveDiagonalHardness

/-! Actual A.10 hard direction for positive invertible symmetric cores with
constant squared row sums. The root extension, endpoint unaries, square gadget,
and prescribed-source answer transport are all constructed. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealSymmetricCoreHard
open DensePolynomial Complexity FixedRealExtension RepresentedBit FixedRealMixedInterpolation
open RelativeWeightedSpectralField PositiveRealCore
variable {n e q:ℕ} {F:Type} [Field F] [Algebra (RationalFunction n) F] [Algebra F ℝ]

 theorem nonconstant_weights_hard (basis:Module.Basis (Fin e) (RationalFunction n) F)
    (M:Matrix (Fin q) (Fin q) F) (w:Fin q→F)
    (hs:∀i j,realMatrix M i j=realMatrix M j i)
    (hM:IsUnit (realMatrix M)) (hp:∀i j,0<realMatrix M i j)
    (r:ℝ) (hr:∀i,∑j,(realMatrix M i j)^2=r)
    (hw:∀i,0<realWeights w i) (hnon:∃i j,w i≠w j) :
    SharpPHard (problem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w) := by
  obtain ⟨a,b,hab⟩:=hnon
  letI : Nonempty (Fin q):=⟨a⟩
  have hnonR:∃i j,realWeights w i≠realWeights w j :=
    ⟨a,b,fun h=>hab ((algebraMap F ℝ).injective h)⟩
  obtain ⟨hpd,hpos,hdiag⟩:=FixedRealCoreObstructions.symmetric_regular_core
    (realMatrix M) hs hM hp r hr (realWeights w) hw hnonR
  let P:=FixedRealSquareRootGram.model basis w hw
  let S:=FixedRealSquareRootGram.square basis M w hw
  have hreal:(fun i j=>algebraMap P.Carrier ℝ (S i j))=
      (PositiveRealCore.decorated (realMatrix M) (realWeights w) (realWeights w))^2 :=
    FixedRealSquareRootGram.square_real basis M w hw
  have hpdS:(show Matrix (Fin q) (Fin q) ℝ from fun i j=>algebraMap P.Carrier ℝ (S i j)).PosDef := by
    rw [hreal]; exact hpd
  have hposS:∀i j,0<algebraMap P.Carrier ℝ (S i j) := by
    intro i j; rw [show algebraMap P.Carrier ℝ (S i j)=_ from congrFun (congrFun hreal i) j]; exact hpos i j
  have hdiagS:∃i j,S i i≠S j j := by
    obtain ⟨i,j,hij⟩:=hdiag
    refine ⟨i,j,?_⟩
    intro he
    apply hij
    have hh:=congrArg (algebraMap P.Carrier ℝ) he
    simpa only [congrFun (congrFun hreal i) i,congrFun (congrFun hreal j) j] using hh
  have hh:=FixedRealApproximation.positive_nonconstant_diagonal_hard P.basis (algebraMap P.Carrier ℝ) S hpdS hposS hdiagS
  exact hh.trans (FixedRealSquareRootGram.sourceReduction basis (fun _:Fin 1=>M)
    (fun u:Fin 0=>u.elim0) w 0 hs hw (unit_rows_nonzero (realMatrix M) hM)
      (fun i j hij t=>unit_rows_nonproportional (realMatrix M) hM hij t))

end PlanarHom.FixedRealSymmetricCoreHard
