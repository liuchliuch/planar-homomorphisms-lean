import PlanarHom.ColoringMacroWireFramedRetention
import PlanarHom.ColoringFramedMacroPorts

/-! The exterior cut retains exactly the original linear source block at
every exposed port. No additional cyclic rotation is hidden in the join. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringMacroFaces.WireFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def closingValue (q : Fin 2646) : ℕ := let a:=prevValue q.val; if a%2=0 then a+1 else a-1
def cutRawRow (v : Fin 534) (q : Fin 2646) : List ℕ :=
  (rawRowValue v.val).rotate ((rawRowValue v.val).idxOf (closingValue q)+1)
def retainedCutRawRow (v : Fin 534) (q : Fin 2646) : List (ℕ×Bool) :=
  ((cutRawRow v q).filter (fun a => decide (a/2<1313))).map (fun a => (a/2,decide (a%2=0)))
theorem leftOldBound : ∀i : Fin 3,(leftVertex i).val<530 := by decide +kernel
theorem rightOldBound : ∀i : Fin 3,(rightVertex i).val<530 := by decide +kernel
def leftOldVertex (i : Fin 3) : Fin 530 := ⟨(leftVertex i).val,leftOldBound i⟩
def rightOldVertex (i : Fin 3) : Fin 530 := ⟨(rightVertex i).val,rightOldBound i⟩
theorem left_retained_cut : ∀i : Fin 3,retainedCutRawRow (leftVertex i) (leftGap i)=ColoringWireMacroRows.raw (leftOldVertex i) := by decide +kernel
theorem right_retained_cut : ∀i : Fin 3,retainedCutRawRow (rightVertex i) (rightGap i)=ColoringWireMacroRows.raw (rightOldVertex i) := by decide +kernel
theorem left_cut_last : ∀i : Fin 3,(cutRawRow (leftVertex i) (leftGap i)).getLast?=some (closingValue (leftGap i)) := by decide +kernel
theorem right_cut_last : ∀i : Fin 3,(cutRawRow (rightVertex i) (rightGap i)).getLast?=some (closingValue (rightGap i)) := by decide +kernel
theorem left_closing_mem : ∀i : Fin 3,closingValue (leftGap i)∈rawRowValue (leftVertex i).val := by decide +kernel
theorem right_closing_mem : ∀i : Fin 3,closingValue (rightGap i)∈rawRowValue (rightVertex i).val := by decide +kernel
theorem closingValue_eq (q : Fin 2646) : closingValue q=(IndexedRotationCertificate.flip 1323 (permutation.symm q)).val := by
  rw [IndexedRotationCertificate.flip_value]
  rfl
end PlanarHom.ColoringMacroFaces.WireFramed
