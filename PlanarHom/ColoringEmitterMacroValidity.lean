import PlanarHom.ColoringEmitterGrowth

/-! NEW kernel-checked finite table obligations for every actual macro address
and edge occurrence. These support unconditional raw numeric graph validity. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Macro
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def AddressValid (k : Kind) (a : Address) : Prop :=
  (a.1=0 ∧ a.2.1 < inputCount k ∧ a.2.2<3) ∨
  (a.1=1 ∧ a.2.1 < outputCount k ∧ a.2.2<3) ∨
  (a.1=2 ∧ a.2.1 < privateCount k ∧ a.2.2=0)

instance (k : Kind) (a : Address) : Decidable (AddressValid k a) := by
  unfold AddressValid
  infer_instance

theorem addresses_valid (k : Kind) : ∀a∈addresses k,AddressValid k a := by
  cases k <;> decide +kernel

theorem addresses_length (k : Kind) : (addresses k).length=vertexCount k := by
  cases k <;> decide +kernel

theorem edges_valid (k : Kind) : ∀e∈edges k,e.1<vertexCount k ∧ e.2<vertexCount k := by
  cases k <;> decide +kernel

theorem addedVertices_eq (k : Kind) : addedVertices k=3*outputCount k+privateCount k := by
  cases k <;> decide

theorem addedVertices_ge (k : Kind) : 105≤addedVertices k := by cases k <;> decide

theorem address_valid (k : Kind) (v : ℕ) (hv:v<vertexCount k) : AddressValid k (address k v) := by
  have hl:v<(addresses k).length := by rw [addresses_length]; exact hv
  simp only [address,List.getElem?_eq_getElem hl,Option.getD_some]
  exact addresses_valid k _ (List.getElem_mem hl)

end PlanarHom.ColoringEmitter.Macro
