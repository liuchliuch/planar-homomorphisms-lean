import PlanarHom.DependentMonomialMachines

/-! Equality in varying bounded-degree fields follows from their literal rational coordinates. -/
noncomputable section
namespace PlanarHom.DependentFieldEqualityMachines
open Complexity RationalCircuits
variable {X : Type} (ex : BitEncoding X) (K : X → Type)
variable [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
variable (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
local notation "e" => DependentFieldListMachines.fieldEncoding K dimension basis
local notation "ev" => DependentFieldCodecs.sigma ex e
local notation "es" => DependentFieldCodecs.pair ex e

theorem fp_coordinates : FP ev BitEncoding.rat.list
    (fun s => List.ofFn ((basis s.1).equivFun s.2)) := by
  have hv : FP ev (ex.prod BitEncoding.rat.list)
      (fun s => (s.1,List.ofFn ((basis s.1).equivFun s.2))) := fp_code_view _ _ _ (fun _ => rfl)
  exact hv.comp (PairProjectionMachines.fp_snd _ _)

/-- Compare at most c coordinates. Padding by zero is exact for two elements of
one field, so no field-equality oracle or dimension-dependent circuit is assumed. -/
theorem fp_equality [∀ x, DecidableEq (K x)] (c : ℕ) (hc : ∀ x, dimension x ≤ c) :
    FP es BitEncoding.bool (fun s : Σ x, K x × K x => decide (s.2.1 = s.2.2)) := by
  have ha := (DependentEncodingMachines.fp_fst ex e e).comp (fp_coordinates ex K dimension basis)
  have hb := (DependentEncodingMachines.fp_snd ex e e).comp (fp_coordinates ex K dimension basis)
  have ht (i : Fin c) := ((ha.comp (DependentMonomialMachines.fp_getD BitEncoding.rat 0 i.val)).pair
    (hb.comp (DependentMonomialMachines.fp_getD BitEncoding.rat 0 i.val))).comp fp_rational_equality
  apply (FiniteRationalCircuits.fp_all es Finset.univ _ ht).congr
  intro s
  simp only [Function.comp_def, Finset.mem_univ, forall_const, decide_eq_true_eq, decide_eq_decide]
  constructor
  · intro h
    apply (basis s.1).equivFun.injective
    funext i
    have hi : i.val < c := i.isLt.trans_le (hc s.1)
    have hh := h ⟨i.val,hi⟩
    simpa using hh
  · intro h i
    rw [h]

end PlanarHom.DependentFieldEqualityMachines
