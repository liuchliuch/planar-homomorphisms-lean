import PlanarHom.ConstantMachines
import PlanarHom.MixedParallelMachines
import PlanarHom.BinarySubtractionMachine
import PlanarHom.CodecSizeBounds

/-! The actual selected-occurrence counter used by joint product interpolation. -/

namespace PlanarHom.Complexity
open Turing PlanarHom.MachineComposition PlanarHom.MachinePairing

private theorem complement_length {α : Type} (test : α→Bool) (xs : List α) :
    (repeatSelected test 0 xs).length+(xs.filter test).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx:test x <;> simp [repeatSelected_cons,hx] <;> omega

namespace MixedCode

/-- Number of marked binary occurrences, counting repetitions and loops. -/
def markedCount (selected : ℕ) (g : MixedCode) : ℕ :=
  (g.edges.filter (fun e=>decide (e.2.2=selected))).length

theorem markedCount_eq_sub (selected : ℕ) (g : MixedCode) :
    g.markedCount selected = g.edges.length-(g.parallelLabel selected 0).edges.length := by
  have h:=complement_length (fun e : ℕ × (ℕ × ℕ)=>decide (e.2.2=selected)) g.edges
  change (g.edges.filter _).length = g.edges.length-(repeatSelected _ 0 g.edges).length
  omega

theorem markedCount_le_edges (selected : ℕ) (g : MixedCode) : g.markedCount selected≤g.edges.length := by
  exact List.length_filter_le _ _

theorem markedCount_le_input (selected : ℕ) (g : MixedCode) :
    g.markedCount selected≤(encoding.encode g).length :=
  (markedCount_le_edges selected g).trans (edges_le_length g)

noncomputable def edgeCountComputer :
    TM2ComputableInPolyTime encoding.toFinEncoding BitEncoding.nat.toFinEncoding (fun g=>g.edges.length) :=
  composeComputers edgesComputer
    (ListCodecMachines.lengthComputer (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)))

/-- The counter is an actual TM2 construction: preserve the original input,
remove just the selected occurrences, extract both encoded counts, and subtract. -/
noncomputable def markedCountComputer (selected : ℕ) :
    TM2ComputableInPolyTime encoding.toFinEncoding BitEncoding.nat.toFinEncoding (markedCount selected) := by
  let paired := pairComputers (ConstantMachines.computer encoding BitEncoding.unaryNat 0)
    (Turing.idComputableInPolyTime encoding.toFinEncoding)
  let deleted := composeComputers paired (MixedParallelMachines.parallelComputer selected)
  let remaining := composeComputers deleted edgeCountComputer
  let counts := pairComputers edgeCountComputer remaining
  let result := composeComputers counts PlanarHom.BinaryArithmetic.subtractionComputable
  change TM2ComputableInPolyTime encoding.toFinEncoding BitEncoding.nat.toFinEncoding
    (fun g=>g.edges.length-(g.parallelLabel selected 0).edges.length) at result
  have he : (fun g : MixedCode=>g.edges.length-(g.parallelLabel selected 0).edges.length)=markedCount selected := by
    funext g
    exact (markedCount_eq_sub selected g).symm
  rw [he] at result
  exact result

theorem fp_markedCount (selected : ℕ) : FP encoding BitEncoding.nat (markedCount selected) :=
  ⟨markedCountComputer selected⟩

end MixedCode
end PlanarHom.Complexity
