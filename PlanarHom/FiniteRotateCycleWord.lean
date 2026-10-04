import PlanarHom.FinitePermutationCyclicEmbedding
import Mathlib.GroupTheory.Perm.Fin

/-! NEW literal full cycle word of the finite successor permutation. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open FinitePermutationReturnWords

 theorem finRotate_val (N:ℕ) (i:Fin N) : (finRotate N i).val=(i.val+1)%N := by
  cases N with
  | zero => exact i.elim0
  | succ N => simp [finRotate_succ_apply,Fin.val_add,Nat.add_mod]

 theorem finRotate_iterate_zero_val (N:ℕ) (hN:0<N) (k:ℕ) :
    ((finRotate N)^[k] ⟨0,hN⟩).val=k%N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',finRotate_val,ih]
    simp [Nat.add_mod]

 theorem finRotate_cycleWord (N:ℕ) (hN:0<N) : cycleWord (finRotate N) ⟨0,hN⟩=List.finRange N := by
  have hw:orbitPrefix (finRotate N) N ⟨0,hN⟩=List.finRange N:=by
    apply List.ext_getElem (by simp)
    intro i hi hj
    apply Fin.ext
    have hi':i<N:=by simpa only [orbitPrefix_length] using hi
    simp only [orbitPrefix,List.getElem_map,List.getElem_range,List.getElem_finRange]
    exact (finRotate_iterate_zero_val N hN i).trans (Nat.mod_eq_of_lt hi')
  have hp:=period_eq_of_prefix_nodup (finRotate N) ⟨0,hN⟩ N hN
    (by apply Fin.ext;simpa using finRotate_iterate_zero_val N hN N)
    (hw.symm ▸ List.nodup_finRange N)
  simpa only [cycleWord,hp] using hw

end PlanarHom.FinitePermutationCycles
