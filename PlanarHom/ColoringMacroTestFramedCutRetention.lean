import PlanarHom.ColoringMacroTestFramedRetention
import PlanarHom.ColoringFramedMacroPorts

/-! The exterior cut retains exactly the original linear source block at
every exposed port. No additional cyclic rotation is hidden in the join. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def closingValue (q : Fin 570) : ℕ := let a:=prevValue q.val; if a%2=0 then a+1 else a-1
def cutRawRow (v : Fin 118) (q : Fin 570) : List ℕ :=
  (rawRowValue v.val).rotate ((rawRowValue v.val).idxOf (closingValue q)+1)
def retainedCutRawRow (v : Fin 118) (q : Fin 570) : List (ℕ×Bool) :=
  ((cutRawRow v q).filter (fun a => decide (a/2<272))).map (fun a => (a/2,decide (a%2=0)))
theorem leftOldBound : ∀i : Fin 9,(leftVertex i).val<114 := by decide +kernel
theorem rightOldBound : ∀i : Fin 0,(rightVertex i).val<114 := by decide +kernel
def leftOldVertex (i : Fin 9) : Fin 114 := ⟨(leftVertex i).val,leftOldBound i⟩
def rightOldVertex (i : Fin 0) : Fin 114 := ⟨(rightVertex i).val,rightOldBound i⟩
theorem left_retained_cut : ∀i : Fin 9,retainedCutRawRow (leftVertex i) (leftGap i)=ColoringTestMacroRows.raw (leftOldVertex i) := by decide +kernel
theorem right_retained_cut : ∀i : Fin 0,retainedCutRawRow (rightVertex i) (rightGap i)=ColoringTestMacroRows.raw (rightOldVertex i) := by decide +kernel
theorem left_cut_last : ∀i : Fin 9,(cutRawRow (leftVertex i) (leftGap i)).getLast?=some (closingValue (leftGap i)) := by decide +kernel
theorem right_cut_last : ∀i : Fin 0,(cutRawRow (rightVertex i) (rightGap i)).getLast?=some (closingValue (rightGap i)) := by decide +kernel
theorem left_closing_mem : ∀i : Fin 9,closingValue (leftGap i)∈rawRowValue (leftVertex i).val := by decide +kernel
theorem right_closing_mem : ∀i : Fin 0,closingValue (rightGap i)∈rawRowValue (rightVertex i).val := by decide +kernel
theorem closingValue_eq (q : Fin 570) : closingValue q=(IndexedRotationCertificate.flip 285 (permutation.symm q)).val := by
  rw [IndexedRotationCertificate.flip_value]
  rfl
end PlanarHom.ColoringMacroFaces.TestFramed
