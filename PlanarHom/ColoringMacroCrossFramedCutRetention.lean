import PlanarHom.ColoringMacroCrossFramedRetention
import PlanarHom.ColoringFramedMacroPorts

/-! The exterior cut retains exactly the original linear source block at
every exposed port. No additional cyclic rotation is hidden in the join. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringMacroFaces.CrossFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def closingValue (q : Fin 6336) : ℕ := let a:=prevValue q.val; if a%2=0 then a+1 else a-1
def cutRawRow (v : Fin 1274) (q : Fin 6336) : List ℕ :=
  (rawRowValue v.val).rotate ((rawRowValue v.val).idxOf (closingValue q)+1)
def retainedCutRawRow (v : Fin 1274) (q : Fin 6336) : List (ℕ×Bool) :=
  ((cutRawRow v q).filter (fun a => decide (a/2<3152))).map (fun a => (a/2,decide (a%2=0)))
theorem leftOldBound : ∀i : Fin 6,(leftVertex i).val<1270 := by decide +kernel
theorem rightOldBound : ∀i : Fin 6,(rightVertex i).val<1270 := by decide +kernel
def leftOldVertex (i : Fin 6) : Fin 1270 := ⟨(leftVertex i).val,leftOldBound i⟩
def rightOldVertex (i : Fin 6) : Fin 1270 := ⟨(rightVertex i).val,rightOldBound i⟩
theorem left_retained_cut : ∀i : Fin 6,retainedCutRawRow (leftVertex i) (leftGap i)=ColoringCrossMacroRows.raw (leftOldVertex i) := by decide +kernel
theorem right_retained_cut : ∀i : Fin 6,retainedCutRawRow (rightVertex i) (rightGap i)=ColoringCrossMacroRows.raw (rightOldVertex i) := by decide +kernel
theorem left_cut_last : ∀i : Fin 6,(cutRawRow (leftVertex i) (leftGap i)).getLast?=some (closingValue (leftGap i)) := by decide +kernel
theorem right_cut_last : ∀i : Fin 6,(cutRawRow (rightVertex i) (rightGap i)).getLast?=some (closingValue (rightGap i)) := by decide +kernel
theorem left_closing_mem : ∀i : Fin 6,closingValue (leftGap i)∈rawRowValue (leftVertex i).val := by decide +kernel
theorem right_closing_mem : ∀i : Fin 6,closingValue (rightGap i)∈rawRowValue (rightVertex i).val := by decide +kernel
theorem closingValue_eq (q : Fin 6336) : closingValue q=(IndexedRotationCertificate.flip 3168 (permutation.symm q)).val := by
  rw [IndexedRotationCertificate.flip_value]
  rfl
end PlanarHom.ColoringMacroFaces.CrossFramed
