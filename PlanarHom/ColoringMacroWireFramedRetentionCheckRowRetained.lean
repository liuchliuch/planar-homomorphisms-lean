import PlanarHom.ColoringMacroWireFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem row_retained_b0 : ∀ i : Fin 48, retainedRawRow ⟨(0+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(0+i.val)%530,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b1 : ∀ i : Fin 48, retainedRawRow ⟨(48+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(48+i.val)%530,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b2 : ∀ i : Fin 48, retainedRawRow ⟨(96+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(96+i.val)%530,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b3 : ∀ i : Fin 48, retainedRawRow ⟨(144+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(144+i.val)%530,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b4 : ∀ i : Fin 48, retainedRawRow ⟨(192+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(192+i.val)%530,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b5 : ∀ i : Fin 48, retainedRawRow ⟨(240+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(240+i.val)%530,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b6 : ∀ i : Fin 48, retainedRawRow ⟨(288+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(288+i.val)%530,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b7 : ∀ i : Fin 48, retainedRawRow ⟨(336+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(336+i.val)%530,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b8 : ∀ i : Fin 48, retainedRawRow ⟨(384+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(384+i.val)%530,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b9 : ∀ i : Fin 48, retainedRawRow ⟨(432+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(432+i.val)%530,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b10 : ∀ i : Fin 48, retainedRawRow ⟨(480+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(480+i.val)%530,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b11 : ∀ i : Fin 2, retainedRawRow ⟨(528+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(528+i.val)%530,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_n0_0 : ∀ i : Fin 96, retainedRawRow ⟨(0+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(0+i.val)%530,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨i%530,Nat.mod_lt _ (by decide)⟩) 0 48 48 row_retained_b0 row_retained_b1

private theorem row_retained_n0_1 : ∀ i : Fin 96, retainedRawRow ⟨(96+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(96+i.val)%530,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨i%530,Nat.mod_lt _ (by decide)⟩) 96 48 48 row_retained_b2 row_retained_b3

private theorem row_retained_n0_2 : ∀ i : Fin 96, retainedRawRow ⟨(192+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(192+i.val)%530,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨i%530,Nat.mod_lt _ (by decide)⟩) 192 48 48 row_retained_b4 row_retained_b5

private theorem row_retained_n0_3 : ∀ i : Fin 96, retainedRawRow ⟨(288+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(288+i.val)%530,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨i%530,Nat.mod_lt _ (by decide)⟩) 288 48 48 row_retained_b6 row_retained_b7

private theorem row_retained_n0_4 : ∀ i : Fin 96, retainedRawRow ⟨(384+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(384+i.val)%530,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨i%530,Nat.mod_lt _ (by decide)⟩) 384 48 48 row_retained_b8 row_retained_b9

private theorem row_retained_n0_5 : ∀ i : Fin 50, retainedRawRow ⟨(480+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(480+i.val)%530,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨i%530,Nat.mod_lt _ (by decide)⟩) 480 48 2 row_retained_b10 row_retained_b11

private theorem row_retained_n1_0 : ∀ i : Fin 192, retainedRawRow ⟨(0+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(0+i.val)%530,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨i%530,Nat.mod_lt _ (by decide)⟩) 0 96 96 row_retained_n0_0 row_retained_n0_1

private theorem row_retained_n1_1 : ∀ i : Fin 192, retainedRawRow ⟨(192+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(192+i.val)%530,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨i%530,Nat.mod_lt _ (by decide)⟩) 192 96 96 row_retained_n0_2 row_retained_n0_3

private theorem row_retained_n1_2 : ∀ i : Fin 146, retainedRawRow ⟨(384+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(384+i.val)%530,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨i%530,Nat.mod_lt _ (by decide)⟩) 384 96 50 row_retained_n0_4 row_retained_n0_5

private theorem row_retained_n2_0 : ∀ i : Fin 384, retainedRawRow ⟨(0+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(0+i.val)%530,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨i%530,Nat.mod_lt _ (by decide)⟩) 0 192 192 row_retained_n1_0 row_retained_n1_1

private theorem row_retained_n3_0 : ∀ i : Fin 530, retainedRawRow ⟨(0+i.val)%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨(0+i.val)%530,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨i%530,Nat.mod_lt _ (by decide)⟩) 0 384 146 row_retained_n2_0 row_retained_n1_2

theorem row_retained : ∀ i : Fin 530, retainedRawRow ⟨i.val%530,Nat.mod_lt _ (by decide)⟩=ColoringWireMacroRows.raw ⟨i.val%530,Nat.mod_lt _ (by decide)⟩ := by
  simpa only [Nat.zero_add] using row_retained_n3_0

end PlanarHom.ColoringMacroFaces.WireFramed
