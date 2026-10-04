import PlanarHom.MixedLabelExpansionPlanarity
import PlanarHom.PrescribedDomainQueryPromises

/-! Label words preserve the exact domain assignment and all reserved unary
occurrences. Each factor is checked against the original endpoint-domain pair. -/
namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode FiniteLabelWordLookupMachines
variable {a b d ut : ℕ}

theorem expandBinaryWords_withDomains (ρ : Fin a→List (Fin b)) (g : MixedCode)
    (δ : Fin g.vertices→Fin d) :
    (withDomains (unaryTypes:=ut) g δ).expandBinaryWords (finTable ρ)=
      withDomains (unaryTypes:=ut) (g.expandBinaryWords (finTable ρ)) δ := rfl

theorem Typed.expandBinaryWords (ρ : Fin a→List (Fin b))
    {BT : Fin a→Fin d→Fin d→Prop} {BS : Fin b→Fin d→Fin d→Prop} {U : Fin ut→Fin d→Prop}
    (hB : ∀i x y,BT i x y→∀j∈ρ i,BS j x y)
    {g : MixedCode} {hg : g.Valid a ut} {δ : Fin g.vertices→Fin d} (h : Typed BT U g hg δ) :
    Typed BS U (g.expandBinaryWords (finTable ρ))
      (expandBinaryWords_valid _ hg (lookup_finTable_lt ρ)) δ := by
  refine ⟨?_,h.2⟩
  intro e he
  obtain ⟨old,hold,hword⟩ := List.mem_flatMap.mp he
  obtain ⟨label,hlabel,rfl⟩ := List.mem_map.mp hword
  have hv := hg.1 old hold
  rw [lookup_finTable ρ ⟨old.2.2,hv.2.2⟩] at hlabel
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hlabel
  exact hB _ _ _ (h.1 old hold) j hj

theorem EncodedGraph.expandBinaryWords (ρ : Fin a→List (Fin b))
    {BT : Fin a→Fin d→Fin d→Prop} {BS : Fin b→Fin d→Fin d→Prop} {U : Fin ut→Fin d→Prop}
    (hB : ∀i x y,BT i x y→∀j∈ρ i,BS j x y)
    {g : MixedCode} (h : EncodedGraph BT U g) :
    EncodedGraph BS U (g.expandBinaryWords (finTable ρ)) := by
  obtain ⟨original,hg,δ,ht,hp,hd⟩ := h
  rw [MixedCode.encoding.decode_encode] at hd
  have he : g=withDomains (unaryTypes:=ut) original δ := Option.some.inj hd
  subst g
  unfold EncodedGraph
  rw [expandBinaryWords_withDomains]
  exact encodedInput_encode_withDomains (ht.expandBinaryWords ρ hB)
    (expandBinaryWords_planar _ ⟨hg,hp⟩ (lookup_finTable_lt ρ)).2

end PlanarHom.PrescribedDomains
