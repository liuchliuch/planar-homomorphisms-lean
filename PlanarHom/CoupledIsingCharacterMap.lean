import PlanarHom.BinaryLinearCharacters
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The exact binary character map, its literal image, and equivalence of
surjectivity with linear independence of the coupling labels. -/
noncomputable section
open Classical
namespace PlanarHom.CoupledIsing
open BinaryCharacters
variable {n m:ℕ}

def characterMap (a:Fin m→Space n) : Space n→ₗ[F₂]Space m := Matrix.mulVecLin a
abbrev ImageSpace (a:Fin m→Space n) := LinearMap.range (characterMap a)
def toImage (a:Fin m→Space n) : Space n→ₗ[F₂]ImageSpace a := (characterMap a).rangeRestrict

theorem toImage_surjective (a:Fin m→Space n) : Function.Surjective (toImage a) := by
  rintro ⟨y,⟨x,hx⟩⟩
  exact ⟨x,Subtype.ext hx⟩

def coordinate (a:Fin m→Space n) (r:Fin m) : ImageSpace a→ₗ[F₂]F₂ :=
  (LinearMap.proj r).comp (LinearMap.range (characterMap a)).subtype

theorem coordinate_toImage (a:Fin m→Space n) (r:Fin m) (x:Space n) :
    coordinate a r (toImage a x)=functional (a r) x := rfl

theorem coordinate_injective (a:Fin m→Space n) (ha:Function.Injective a) :
    Function.Injective (coordinate a) := by
  intro r s h
  apply ha
  apply functional_injective
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun h (toImage a x)

theorem coordinate_ne_zero (a:Fin m→Space n) (ha:∀r,a r≠0) (r:Fin m) :
    coordinate a r≠0 := by
  intro h
  apply ha r
  apply functional_injective
  apply LinearMap.ext
  intro x
  have hh:=LinearMap.congr_fun h (toImage a x)
  simpa [functional] using hh

theorem map_surjective_iff_independent (a:Fin m→Space n) :
    Function.Surjective (characterMap a) ↔ LinearIndependent F₂ a := by
  constructor
  · intro h
    have hr:Matrix.rank a=m := by
      change Module.finrank F₂ (LinearMap.range (characterMap a))=m
      rw [LinearMap.range_eq_top.mpr h]
      simp
    apply (linearIndependent_iff_card_eq_finrank_span (K:=F₂) (b:=a)).mpr
    simpa only [Matrix.rank_eq_finrank_span_row,Matrix.row,Fintype.card_fin] using hr.symm
  · intro h
    have hr:=h.rank_matrix
    have hf:Module.finrank F₂ (LinearMap.range (characterMap a))=Module.finrank F₂ (Space m) := by
      simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,smul_eq_mul,mul_one] using hr
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hf)

end PlanarHom.CoupledIsing
