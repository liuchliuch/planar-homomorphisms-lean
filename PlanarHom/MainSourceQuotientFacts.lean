import PlanarHom.MainSourceColorTransport

/-! Source-closed row injectivity and actual quotient symmetry/nonnegativity.
The zero class and summed original weights remain in the quotient. -/
noncomputable section
open Classical
namespace PlanarHom.RootedRestriction
variable {C K : Type} [Field K]

theorem closed_rows_injective (M : Matrix C C K) (hinj : Function.Injective M)
    (X : Set C) (hX : ColorClosed M X) :
    Function.Injective (fun i j : X=>M i.val j.val) := by
  intro i j h
  apply Subtype.ext
  apply hinj
  funext k
  by_cases hk:k∈X
  · exact congrFun h ⟨k,hk⟩
  · have hi : M i.val k=0 := by by_contra hn; exact hk (hX i.val i.property k hn)
    have hj : M j.val k=0 := by by_contra hn; exact hk (hX j.val j.property k hn)
    rw [hi,hj]

end PlanarHom.RootedRestriction
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity RootedRestriction Structures
variable {q : ℕ}

theorem main_supportFinite_rows_injective (L : RealLanguage q 1 0)
    (hinj : Function.Injective (L.matrices 0)) (X : Set (Fin q)) [Fintype X]
    (hX : ColorClosed (L.matrices 0) X) :
    Function.Injective ((L.supportFiniteLanguage X).matrices 0) := by
  let e := (Fintype.equivFin X).symm
  have hi := closed_rows_injective (L.matrices 0) hinj X hX
  intro i j he
  apply e.injective
  apply hi
  funext k
  have h := congrFun he (e.symm k)
  change L.matrices 0 (e i).val (e (e.symm k)).val=
    L.matrices 0 (e j).val (e (e.symm k)).val at h
  rw [e.apply_symm_apply] at h
  exact h

theorem main_fullQuotient_symmetric (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :
    ∀ i j,(L.fullQuotientLanguage hs).matrices 0 i j=(L.fullQuotientLanguage hs).matrices 0 j i := by
  intro i j
  exact congrArg L.field.val (FiniteFieldQuotientLanguage.matrix_symmetric
    (L.matricesK 0) (L.actualTwin_symmetryK hs) i j)

theorem main_fullQuotient_nonnegative (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) :
    ∀ i j,0≤(L.fullQuotientLanguage hs).matrices 0 i j := by
  intro i j
  change 0≤(FiniteFieldQuotientLanguage.matrix (L.matricesK 0) (L.actualTwin_symmetryK hs) i j:ℝ)
  rw [FiniteFieldQuotientLanguage.matrix_entry]
  exact hnn _ _

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
