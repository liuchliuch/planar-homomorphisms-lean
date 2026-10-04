import PlanarHom.ProductRepresentativeSemantics
import PlanarHom.LagrangeCoefficientMachines

/-! Source-word promises for the actual computed node table and all its sublists. -/

namespace PlanarHom.ExponentProductTables
open PlanarHom.LagrangeCoefficientMachines PlanarHom.ExponentProductSemantics
variable {K : Type} [Field K] [DecidableEq K] {t : ℕ}

/-- Each actual retained row contains source/target products of the same length-m word. -/
theorem representative_word (A B : Fin t → K) (m : ℕ) (p : K × K)
    (hp : p ∈ representatives A B m) :
    ∃ word : List (Fin t), word.length = m ∧ (word.map A).prod = p.1 ∧ (word.map B).prod = p.2 := by
  have hm := (representatives_sublist A B m).subset hp
  rw [products_list_form] at hm
  obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hm
  have hx := (PlanarHom.ExponentVectors.mem_weak t m xs).mp hxs
  exact ⟨expand t xs, (expand_length xs hx.1).trans hx.2, expand_product A xs, expand_product B xs⟩

/-- The complete computed node list satisfies the promised coefficient-machine input type. -/
theorem source_nodes_valid (A B : Fin t → K) (m : ℕ) :
    NodesValid A m ((representatives A B m).map Prod.fst) := by
  intro μ hμ
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hμ
  obtain ⟨word, hlen, hs, _⟩ := representative_word A B m p hp
  exact ⟨word, hlen, hs⟩

/-- Removing the current interpolation node retains the same source-word promise. -/
theorem source_nodes_valid_of_sublist (A B : Fin t → K) (m : ℕ) (xs : List K)
    (hxs : xs.Sublist ((representatives A B m).map Prod.fst)) : NodesValid A m xs :=
  fun μ hμ => source_nodes_valid A B m μ (hxs.subset hμ)

/-- Target representatives themselves obey the fixed target-alphabet height promise. -/
theorem target_nodes_valid (A B : Fin t → K) (m : ℕ) :
    NodesValid B m ((representatives A B m).map Prod.snd) := by
  intro μ hμ
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hμ
  obtain ⟨word, hlen, _, ht⟩ := representative_word A B m p hp
  exact ⟨word, hlen, ht⟩

end PlanarHom.ExponentProductTables
