import PlanarHom.ColoringEmitter
import PlanarHom.CountingPositiveOneInThreeHardness

/-! NEW exact empty-source branch of the actual emitter and recovery code. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open Complexity ParsimoniousNorOneInThree ProperColoringPottsReduction

 theorem source_count_empty (n:ℕ) : CountingPositiveOneInThree.count (n,[])=2^n := by
  simp [CountingPositiveOneInThree.count,NorExactOne.Solutions,Satisfies]

 theorem totalColorings_empty (n:ℕ) : totalColorings 3 (compile (n,[]))=1 := by
  simp [compile,totalColorings,MixedCode.Valid,properColoringCount]

 theorem recover_empty_correct (n:ℕ) :
    recover ((n,[]),[totalColorings 3 (compile (n,[]))])=CountingPositiveOneInThree.count (n,[]) := by
  rw [recover_empty,totalColorings_empty,source_count_empty]
  simp

 theorem compile_empty_planarValid (n:ℕ) : (compile (n,[])).PlanarValid 1 0 := by
  apply (MixedCode.planarValid_iff (compile (n,[])) (compile_valid (n,[]))).mpr
  exact ⟨{
    point:=Fin.elim0
    point_injective:=fun v=>Fin.elim0 v
    curve:=Fin.elim0
    curve_zero:=fun e=>Fin.elim0 e
    curve_one:=fun e=>Fin.elim0 e
    interior_injective:=fun e=>Fin.elim0 e
    interior_avoids:=fun e=>Fin.elim0 e }⟩

end PlanarHom.ColoringEmitter
