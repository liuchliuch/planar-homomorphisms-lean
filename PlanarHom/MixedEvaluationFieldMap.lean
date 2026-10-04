import PlanarHom.PrescribedDomains

/-!
# Field-map transport of actual mixed evaluation

A coefficient ring homomorphism commutes with every actual assignment sum,
occurrence product and fixed background factor. Prescribed-domain restrictions
and their reserved intrinsic indicators are retained exactly.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode
variable {C K L : Type} [Fintype C] [CommSemiring K] [CommSemiring L]
variable {binaryTypes unaryTypes : ℕ}

@[simp] theorem map_binaryValue (φ : K →+* L) (vertices : ℕ)
    (M : Fin binaryTypes → Matrix C C K) (σ : Fin vertices → C) (e : ℕ × (ℕ × ℕ)) :
    φ (binaryValue vertices binaryTypes M σ e) =
      binaryValue vertices binaryTypes (fun l i j => φ (M l i j)) σ e := by
  unfold binaryValue
  split <;> simp

@[simp] theorem map_unaryValue (φ : K →+* L) (vertices : ℕ)
    (U : Fin unaryTypes → C → K) (σ : Fin vertices → C) (e : ℕ × ℕ) :
    φ (unaryValue vertices unaryTypes U σ e) =
      unaryValue vertices unaryTypes (fun l i => φ (U l i)) σ e := by
  unfold unaryValue
  split <;> simp

/-- Exact transport of the original weighted mixed partition function through a
ring homomorphism. Loops, multiplicity, zeros, unaries and isolates remain in place. -/
theorem map_evaluate (φ : K →+* L) (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (M : Fin binaryTypes → Matrix C C K) (U : Fin unaryTypes → C → K) (w : C → K) :
    φ (g.evaluate hg M U w) =
      g.evaluate hg (fun l i j => φ (M l i j)) (fun l i => φ (U l i)) (fun i => φ (w i)) := by
  simp only [evaluate, map_sum, map_mul, map_prod, map_list_prod, List.map_map,
    Function.comp_def, map_binaryValue, map_unaryValue]

end PlanarHom.Complexity.MixedCode

namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode
attribute [local instance] Classical.propDecidable
variable {C K L : Type} [Fintype C] [CommSemiring K] [CommSemiring L]
variable {binaryTypes unaryTypes domainTypes : ℕ}

/-- Intrinsic domain indicators are unchanged by the coefficient field map. -/
@[simp] theorem map_indicator (φ : K →+* L) (D : Set C) (c : C) :
    φ (indicator (R := K) D c) = indicator (R := L) D c := by
  by_cases h : c ∈ D <;> simp [indicator, h]

/-- The actual prescribed assignment sets are not changed by field transport. -/
theorem map_evaluateRestricted (φ : K →+* L) (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (M : Fin binaryTypes → Matrix C C K) (U : Fin unaryTypes → C → K) (w : C → K)
    (D : Fin domainTypes → Set C) (δ : Fin g.vertices → Fin domainTypes) :
    φ (evaluateRestricted g hg M U w D δ) =
      evaluateRestricted g hg (fun l i j => φ (M l i j)) (fun l i => φ (U l i))
        (fun i => φ (w i)) D δ := by
  unfold evaluateRestricted
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split <;> simp only [map_mul, map_prod, map_list_prod, List.map_map, Function.comp_def,
    map_binaryValue, map_unaryValue, map_zero]

/-- Reserved labels keep exactly their domain-indicator interpretation after
mapping every original unary value into a common field. -/
theorem map_extendedUnaries (φ : K →+* L) (U : Fin unaryTypes → C → K)
    (D : Fin domainTypes → Set C) :
    (fun l c => φ (extendedUnaries U D l c)) =
      extendedUnaries (fun l c => φ (U l c)) D := by
  funext l c
  refine Fin.addCases ?_ ?_ l
  · intro i
    simp [extendedUnaries]
  · intro i
    simp [extendedUnaries]

end PlanarHom.PrescribedDomains
