import PlanarHom.TypedGadgetAppendColoredTemplates

/-! The encoded intrinsic records are exactly the prescribed private
assignment restriction, rather than an independently available unary language. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedGadgetNetwork
open PrescribedDomains
variable {C R : Type} [Fintype C] [CommSemiring R] {p e bt ut dt : ℕ}

/-- Exact finite sum over private assignments satisfying their individual
fixed domains. Boundary colors remain arguments and receive no gadget pin. -/
theorem ofTypedColoredTwoTerminal_signature_restricted (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt)
    (M : Fin bt → Matrix C C R) (U : Fin ut → C → R)
    (D : Fin dt → Set C) (τ : Fin 2 → C) :
    templateSignature (ofTypedColoredTwoTerminal G label tag ut) M (extendedUnaries U D) τ =
      ∑ η : {η : Fin p → C // Allowed D tag η},
        ∏ i, M (label i) (TwoTerminal.extend (τ 0) (τ 1) η.val (G.src i))
          (TwoTerminal.extend (τ 0) (τ 1) η.val (G.dst i)) := by
  rw [ofTypedColoredTwoTerminal_signature_domains]
  rw [←Finset.sum_subtype (Finset.univ.filter (Allowed D tag)) (by simp)
    (fun η : Fin p → C=>∏ i, M (label i) (TwoTerminal.extend (τ 0) (τ 1) η (G.src i))
      (TwoTerminal.extend (τ 0) (τ 1) η (G.dst i)))]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro η _
  rw [indicator_product]
  split_ifs <;> simp

end PlanarHom.FixedGadgetNetwork
