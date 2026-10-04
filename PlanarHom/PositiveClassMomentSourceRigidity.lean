import PlanarHom.PositiveClassMomentWeightBridge
import PlanarHom.PositiveUnitDiagonalSourceRigidity
import PlanarHom.ZeroOneGramSourceAvailability

/-! Conditional source-level positive class-moment rigidity. General positive
Potts hardness is an explicit parameter at this intermediate layer: invertibility, both classified
matrix availabilities, the common cube chart, and the unit-background + unary
entrance are proved from the actual normalized weighted source. This is an
intermediate necessity theorem, used in the closed classifications in Sections 8 and 11. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveClassMomentRigidity
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity FiniteLanguageAliases ClosedMatrixFamily
variable {q bt ut : ℕ} [Nonempty (Fin q)]

/-- An existing positive unary in a unit-background retained language must be
constant. The actual8.2 source rigidity supplies nonsingularity, and both PD
matrices are classified through actual source reductions. Their constant
diagonals suffice, so the proof does not require choosing a shared chart. -/
theorem unary_constant_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q bt ut) (old : Fin bt) (selected : Fin ut)
    (hunit : ∀ i,L.weights i=1)
    (hs : ∀ i j,L.matrices old i j=L.matrices old j i)
    (hpos : ∀ i j,0<L.matrices old i j) (hdiag : ∀ i,L.matrices old i i=1)
    (hinj : Function.Injective (L.matrices old)) (hμ : ∀ i,0<L.unaries selected i)
    (hnot : ¬PromisedSharpPHard L.problem) : ∀ i j,L.unaries selected i=L.unaries selected j := by
  obtain ⟨_,_,_,_,_,hU⟩ := unit_diagonal_tensor_of_not_hard hPotts L old hunit hs hpos hdiag hinj hnot
  let C := L.matrices old
  let μ := L.unaries selected
  have hCs : C.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using hs j i
  let S := unitLanguage (fun _:Fin 1=>C) (fun _=>L.matrices_algebraic old)
  have rS := S.relabelReduction L (fun _=>old) (fun u:Fin 0=>u.elim0)
    (fun _ _ _=>rfl) (fun u=>u.elim0) (fun i=>(hunit i).symm)
  let Q := S.gramLanguage 1
  have hQmat : Q.matrices 0=C*C := by
    ext i j
    simp [Q,gramLanguage,gramMatrix,PositiveWeightRemoval.gramCoreField,S,unitLanguage,
      Matrix.diagonal_one]
  have hQpd := square_posDef C hCs hU
  have hQpos := square_positive C hpos
  have hQred := (S.gramSourceReduction (fun _=>rfl) 1).trans rS
  have hQnot : ¬PromisedSharpPHard Q.problem := fun hh=>hnot (hh.trans hQred)
  have hQpd' : (Q.matrices 0).PosDef := by rw [hQmat]; exact hQpd
  have hQpos' : ∀i j,0<Q.matrices 0 i j := by intro i j; rw [hQmat]; exact hQpos i j
  have hQform : PositiveDefiniteTensorForm (C*C) := by
    have h := Q.positiveDefiniteTensorForm_of_not_hard hPotts (fun _=>rfl)
      hQpd' (fun i j=>(hQpos' i j).le)
      (support_connected_of_positive_entries _ hQpd'.1 hQpos') hQnot
    rwa [hQmat] at h
  let N := momentSquare C μ
  have hNalg := momentSquare_algebraic C (L.matrices_algebraic old) μ (fun i=>(hμ i).le)
    (L.unaries_algebraic selected)
  let T := L.appendBinary N hNalg
  obtain ⟨rT⟩ := momentSquare_append_available L hunit old selected hμ
  let V := unitLanguage (fun _:Fin 1=>N) (fun _=>hNalg)
  have rV := V.relabelReduction T (fun _=>Fin.last bt) (fun u:Fin 0=>u.elim0)
    (by intro l i j; simp [V,unitLanguage,T,appendBinary,appendOne_aux])
    (fun u=>u.elim0) (fun i=>(hunit i).symm)
  have hVnot : ¬PromisedSharpPHard V.problem := fun hh=>hnot (hh.trans (rV.trans rT))
  have hNpd := momentSquare_posDef C hCs hU μ hμ
  have hNpos := momentSquare_positive C hpos μ hμ
  have hNform : PositiveDefiniteTensorForm N :=
    V.positiveDefiniteTensorForm_of_not_hard hPotts (fun _=>rfl) hNpd
      (fun i j=>(hNpos i j).le) (support_connected_of_positive_entries _ hNpd.1 hNpos) hVnot
  exact moment_constant_of_tensor_forms C μ (fun i=>(hμ i).le) hQform hNform

/-- Literal original positive background weights are constant in the nonhard
case. Rational-power unary availability and background removal are composed
before the preceding common-chart argument, retaining all companion labels. -/
theorem weights_constant_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q bt ut) (old : Fin bt)
    (hs : ∀ i j,L.matrices old i j=L.matrices old j i)
    (hpos : ∀ i j,0<L.matrices old i j) (hdiag : ∀ i,L.matrices old i i=1)
    (hinj : Function.Injective (L.matrices old)) (hw : ∀ i,0<L.weights i)
    (hnot : ¬PromisedSharpPHard L.problem) : ∀ i j,L.weights i=L.weights j := by
  let T := unitWithWeightUnary L
  have red := unitWithWeightUnaryReduction L old hs hpos hdiag hinj hw
  have hnotT : ¬PromisedSharpPHard T.problem := fun hh=>hnot (hh.trans red)
  have hμ : ∀ i,0<T.unaries (Fin.last ut) i := by
    simpa only [T,unitWithWeightUnary,appendOne_aux] using hw
  have he := unary_constant_of_not_hard hPotts T old (Fin.last ut) (fun _=>rfl)
    hs hpos hdiag hinj hμ hnotT
  simpa only [T,unitWithWeightUnary,appendOne_aux] using he

/-- The weighted positive-core hard branch, with the general Potts foundation
explicit and no assumed classification or source-availability interface. -/
theorem nonconstant_weights_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q bt ut) (old : Fin bt)
    (hs : ∀ i j,L.matrices old i j=L.matrices old j i)
    (hpos : ∀ i j,0<L.matrices old i j) (hdiag : ∀ i,L.matrices old i i=1)
    (hinj : Function.Injective (L.matrices old)) (hw : ∀ i,0<L.weights i)
    (hnon : ∃ i j,L.weights i≠L.weights j) : PromisedSharpPHard L.problem := by
  by_contra hnot
  obtain ⟨i,j,hij⟩ := hnon
  exact hij (weights_constant_of_not_hard hPotts L old hs hpos hdiag hinj hw hnot i j)

end PlanarHom.PositiveClassMomentRigidity
