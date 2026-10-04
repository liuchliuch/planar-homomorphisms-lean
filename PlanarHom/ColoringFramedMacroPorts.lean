import PlanarHom.ColoringFramedMacroEuler

noncomputable section
open Classical
namespace PlanarHom.ColoringMacroFaces
open MultiGraph FinitePermutationCycles RadialPotts.Assembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TestFramed
def boundaryVertex : Fin 13 → Fin 118 := ![114,105,106,0,107,108,1,109,110,2,115,116,117]
def leftVertex : Fin 9 → Fin 118 := ![105,106,0,107,108,1,109,110,2]
def rightVertex : Fin 0 → Fin 118 := fun i => i.elim0
def leftGap (i : Fin 9) : Fin 570 := gap ⟨i.val+1,by omega⟩
def rightGap (i : Fin 0) : Fin 570 := gap ⟨13-2-i.val,by omega⟩
theorem boundary_host : ∀ i : Fin 13,host (gap i)=boundaryVertex i := by decide +kernel
theorem boundary_injective : Function.Injective boundaryVertex := by decide +kernel
theorem left_host : ∀ i : Fin 9,host (leftGap i)=leftVertex i := by decide +kernel
theorem right_host : ∀ i : Fin 0,host (rightGap i)=rightVertex i := by decide +kernel
theorem left_injective : Function.Injective leftVertex := by decide +kernel
theorem right_injective : Function.Injective rightVertex := by decide +kernel
theorem left_successor : ∀ i : Fin 8,permutation (leftGap i.succ)=leftGap i.castSucc := by decide +kernel
theorem all_ports_cofacial (i : Fin 9) (j : Fin 0) : permutation.SameCycle (leftGap i) (rightGap j) :=
  all_gaps_sameCycle _ _
end TestFramed
namespace WireFramed
def boundaryVertex : Fin 10 → Fin 534 := ![530,517,518,0,531,532,1,520,519,533]
def leftVertex : Fin 3 → Fin 534 := ![517,518,0]
def rightVertex : Fin 3 → Fin 534 := ![519,520,1]
def leftGap (i : Fin 3) : Fin 2646 := gap ⟨i.val+1,by omega⟩
def rightGap (i : Fin 3) : Fin 2646 := gap ⟨10-2-i.val,by omega⟩
theorem boundary_host : ∀ i : Fin 10,host (gap i)=boundaryVertex i := by decide +kernel
theorem boundary_injective : Function.Injective boundaryVertex := by decide +kernel
theorem left_host : ∀ i : Fin 3,host (leftGap i)=leftVertex i := by decide +kernel
theorem right_host : ∀ i : Fin 3,host (rightGap i)=rightVertex i := by decide +kernel
theorem left_injective : Function.Injective leftVertex := by decide +kernel
theorem right_injective : Function.Injective rightVertex := by decide +kernel
theorem left_successor : ∀ i : Fin 2,permutation (leftGap i.succ)=leftGap i.castSucc := by decide +kernel
theorem right_successor : ∀ i : Fin 2,permutation (rightGap i.castSucc)=rightGap i.succ := by decide +kernel
theorem all_ports_cofacial (i : Fin 3) (j : Fin 3) : permutation.SameCycle (leftGap i) (rightGap j) :=
  all_gaps_sameCycle _ _
end WireFramed
namespace CrossFramed
def boundaryVertex : Fin 16 → Fin 1274 := ![1270,1243,1244,1,1241,1242,0,1271,1272,3,1248,1247,2,1246,1245,1273]
def leftVertex : Fin 6 → Fin 1274 := ![1243,1244,1,1241,1242,0]
def rightVertex : Fin 6 → Fin 1274 := ![1245,1246,2,1247,1248,3]
def leftGap (i : Fin 6) : Fin 6336 := gap ⟨i.val+1,by omega⟩
def rightGap (i : Fin 6) : Fin 6336 := gap ⟨16-2-i.val,by omega⟩
theorem boundary_host : ∀ i : Fin 16,host (gap i)=boundaryVertex i := by decide +kernel
theorem boundary_injective : Function.Injective boundaryVertex := by decide +kernel
theorem left_host : ∀ i : Fin 6,host (leftGap i)=leftVertex i := by decide +kernel
theorem right_host : ∀ i : Fin 6,host (rightGap i)=rightVertex i := by decide +kernel
theorem left_injective : Function.Injective leftVertex := by decide +kernel
theorem right_injective : Function.Injective rightVertex := by decide +kernel
theorem left_successor : ∀ i : Fin 5,permutation (leftGap i.succ)=leftGap i.castSucc := by decide +kernel
theorem right_successor : ∀ i : Fin 5,permutation (rightGap i.castSucc)=rightGap i.succ := by decide +kernel
theorem all_ports_cofacial (i : Fin 6) (j : Fin 6) : permutation.SameCycle (leftGap i) (rightGap j) :=
  all_gaps_sameCycle _ _
end CrossFramed
namespace FanFramed
def boundaryVertex : Fin 13 → Fin 1058 := ![1054,1033,1034,0,1055,1056,1,1036,1035,2,1038,1037,1057]
def leftVertex : Fin 3 → Fin 1058 := ![1033,1034,0]
def rightVertex : Fin 6 → Fin 1058 := ![1037,1038,2,1035,1036,1]
def leftGap (i : Fin 3) : Fin 5264 := gap ⟨i.val+1,by omega⟩
def rightGap (i : Fin 6) : Fin 5264 := gap ⟨13-2-i.val,by omega⟩
theorem boundary_host : ∀ i : Fin 13,host (gap i)=boundaryVertex i := by decide +kernel
theorem boundary_injective : Function.Injective boundaryVertex := by decide +kernel
theorem left_host : ∀ i : Fin 3,host (leftGap i)=leftVertex i := by decide +kernel
theorem right_host : ∀ i : Fin 6,host (rightGap i)=rightVertex i := by decide +kernel
theorem left_injective : Function.Injective leftVertex := by decide +kernel
theorem right_injective : Function.Injective rightVertex := by decide +kernel
theorem left_successor : ∀ i : Fin 2,permutation (leftGap i.succ)=leftGap i.castSucc := by decide +kernel
theorem right_successor : ∀ i : Fin 5,permutation (rightGap i.castSucc)=rightGap i.succ := by decide +kernel
theorem all_ports_cofacial (i : Fin 3) (j : Fin 6) : permutation.SameCycle (leftGap i) (rightGap j) :=
  all_gaps_sameCycle _ _
end FanFramed
end PlanarHom.ColoringMacroFaces
