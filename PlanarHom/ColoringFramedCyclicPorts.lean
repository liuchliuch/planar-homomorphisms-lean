import PlanarHom.ColoringFramedTypedRows
import PlanarHom.IndexedRotationCyclicPorts

/-! NEW checked exterior port order for the four literal framed macro tables.
The small exterior cycles are checked by the kernel; the large interior face
cycles are never enumerated by this proof. -/
noncomputable section
open Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace PlanarHom.ColoringMacroFaces
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles FinitePermutationReturnWords
namespace TestFramed
 def exteriorStart : Fin 570 := permutation.symm (leftGap (Fin.last 8))
 theorem exterior_return : permutation^[13] exteriorStart=exteriorStart := by decide +kernel
 theorem exterior_nodup : (orbitPrefix permutation 13 exteriorStart).Nodup := by decide +kernel
 theorem exterior_period : Function.minimalPeriod permutation exteriorStart=13 :=
  period_eq_of_prefix_nodup permutation exteriorStart 13 (by omega) exterior_return exterior_nodup
 theorem numeric_ports_sublist :
    (((List.ofFn leftGap).reverse++List.ofFn rightGap).map permutation.symm).Sublist
      (orbitPrefix permutation 13 exteriorStart) := by decide +kernel
 theorem numeric_ports_cyclic : CyclicSublist permutation
    (((List.ofFn leftGap).reverse++List.ofFn rightGap).map permutation.symm) := by
  refine ⟨exteriorStart,?_⟩
  rw [cycleWord,exterior_period]
  exact numeric_ports_sublist
 theorem typed_ports_cyclic : CyclicSublist typedRows.facePerm
    ((List.ofFn (fun i=>reversePerm _ (leftClosing i))).reverse++
      List.ofFn (fun i=>reversePerm _ (rightClosing i))) := by
  have hh:=IndexedRotationCertificate.rows_cyclic_markers (n:=118) (m:=285) host permutation rotationCertificate rfl
    ((List.ofFn leftGap).reverse++List.ofFn rightGap) numeric_ports_cyclic
  simpa only [List.map_append,List.map_reverse,List.map_ofFn,leftClosing,rightClosing,typedRows] using hh
end TestFramed
namespace WireFramed
 def exteriorStart : Fin 2646 := permutation.symm (leftGap (Fin.last 2))
 theorem exterior_return : permutation^[10] exteriorStart=exteriorStart := by decide +kernel
 theorem exterior_nodup : (orbitPrefix permutation 10 exteriorStart).Nodup := by decide +kernel
 theorem exterior_period : Function.minimalPeriod permutation exteriorStart=10 :=
  period_eq_of_prefix_nodup permutation exteriorStart 10 (by omega) exterior_return exterior_nodup
 theorem numeric_ports_sublist :
    (((List.ofFn leftGap).reverse++List.ofFn rightGap).map permutation.symm).Sublist
      (orbitPrefix permutation 10 exteriorStart) := by decide +kernel
 theorem numeric_ports_cyclic : CyclicSublist permutation
    (((List.ofFn leftGap).reverse++List.ofFn rightGap).map permutation.symm) := by
  refine ⟨exteriorStart,?_⟩
  rw [cycleWord,exterior_period]
  exact numeric_ports_sublist
 theorem typed_ports_cyclic : CyclicSublist typedRows.facePerm
    ((List.ofFn (fun i=>reversePerm _ (leftClosing i))).reverse++
      List.ofFn (fun i=>reversePerm _ (rightClosing i))) := by
  have hh:=IndexedRotationCertificate.rows_cyclic_markers (n:=534) (m:=1323) host permutation rotationCertificate rfl
    ((List.ofFn leftGap).reverse++List.ofFn rightGap) numeric_ports_cyclic
  simpa only [List.map_append,List.map_reverse,List.map_ofFn,leftClosing,rightClosing,typedRows] using hh
end WireFramed
namespace CrossFramed
 def exteriorStart : Fin 6336 := permutation.symm (leftGap (Fin.last 5))
 theorem exterior_return : permutation^[16] exteriorStart=exteriorStart := by decide +kernel
 theorem exterior_nodup : (orbitPrefix permutation 16 exteriorStart).Nodup := by decide +kernel
 theorem exterior_period : Function.minimalPeriod permutation exteriorStart=16 :=
  period_eq_of_prefix_nodup permutation exteriorStart 16 (by omega) exterior_return exterior_nodup
 theorem numeric_ports_sublist :
    (((List.ofFn leftGap).reverse++List.ofFn rightGap).map permutation.symm).Sublist
      (orbitPrefix permutation 16 exteriorStart) := by decide +kernel
 theorem numeric_ports_cyclic : CyclicSublist permutation
    (((List.ofFn leftGap).reverse++List.ofFn rightGap).map permutation.symm) := by
  refine ⟨exteriorStart,?_⟩
  rw [cycleWord,exterior_period]
  exact numeric_ports_sublist
 theorem typed_ports_cyclic : CyclicSublist typedRows.facePerm
    ((List.ofFn (fun i=>reversePerm _ (leftClosing i))).reverse++
      List.ofFn (fun i=>reversePerm _ (rightClosing i))) := by
  have hh:=IndexedRotationCertificate.rows_cyclic_markers (n:=1274) (m:=3168) host permutation rotationCertificate rfl
    ((List.ofFn leftGap).reverse++List.ofFn rightGap) numeric_ports_cyclic
  simpa only [List.map_append,List.map_reverse,List.map_ofFn,leftClosing,rightClosing,typedRows] using hh
end CrossFramed
namespace FanFramed
 def exteriorStart : Fin 5264 := permutation.symm (leftGap (Fin.last 2))
 theorem exterior_return : permutation^[13] exteriorStart=exteriorStart := by decide +kernel
 theorem exterior_nodup : (orbitPrefix permutation 13 exteriorStart).Nodup := by decide +kernel
 theorem exterior_period : Function.minimalPeriod permutation exteriorStart=13 :=
  period_eq_of_prefix_nodup permutation exteriorStart 13 (by omega) exterior_return exterior_nodup
 theorem numeric_ports_sublist :
    (((List.ofFn leftGap).reverse++List.ofFn rightGap).map permutation.symm).Sublist
      (orbitPrefix permutation 13 exteriorStart) := by decide +kernel
 theorem numeric_ports_cyclic : CyclicSublist permutation
    (((List.ofFn leftGap).reverse++List.ofFn rightGap).map permutation.symm) := by
  refine ⟨exteriorStart,?_⟩
  rw [cycleWord,exterior_period]
  exact numeric_ports_sublist
 theorem typed_ports_cyclic : CyclicSublist typedRows.facePerm
    ((List.ofFn (fun i=>reversePerm _ (leftClosing i))).reverse++
      List.ofFn (fun i=>reversePerm _ (rightClosing i))) := by
  have hh:=IndexedRotationCertificate.rows_cyclic_markers (n:=1058) (m:=2632) host permutation rotationCertificate rfl
    ((List.ofFn leftGap).reverse++List.ofFn rightGap) numeric_ports_cyclic
  simpa only [List.map_append,List.map_reverse,List.map_ofFn,leftClosing,rightClosing,typedRows] using hh
end FanFramed
end PlanarHom.ColoringMacroFaces
