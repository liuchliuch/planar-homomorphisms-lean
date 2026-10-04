import PlanarHom.ParallelSourceRows

/-! Exact positions in each materialized parallel-copy block. -/
noncomputable section
open Classical
namespace PlanarHom.ParallelSource
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {E : Type}

 theorem expand_length (t : ℕ) (xs : List (Dart E)) : (expand t xs).length=xs.length*t := by
  induction xs with
  | nil => simp [expand]
  | cons a xs ih =>
      change (copies t a++expand t xs).length=(xs.length+1)*t
      rw [List.length_append,ih]
      simp [copies,Nat.add_mul,Nat.add_comm]

 theorem block_position_bound {t : ℕ} (xs : List (Dart E)) (i : Fin xs.length) (j : Fin t) :
    i.val*t+j.val<(expand t xs).length := by
  rw [expand_length]
  have hi := i.isLt
  have hj := j.isLt
  nlinarith

 theorem expand_get {t : ℕ} (xs : List (Dart E)) (i : Fin xs.length) (j : Fin t) :
    (expand t xs)[i.val*t+j.val]'(block_position_bound xs i j)=copyDart (xs.get i) j := by
  induction xs with
  | nil => exact i.elim0
  | cons a xs ih =>
      refine Fin.cases ?_ (fun k => ?_) i
      · change (copies t a++expand t xs)[0*t+j.val]'_=copyDart a j
        rw [List.getElem_append_left (by simpa [copies] using j.isLt)]
        simp [copies]
      · change (copies t a++expand t xs)[k.succ.val*t+j.val]'_=copyDart (xs.get k) j
        rw [List.getElem_append_right (by simp only [copies,List.length_map,List.length_finRange,Fin.val_succ]; nlinarith)]
        have he : k.succ.val*t+j.val-(copies t a).length=k.val*t+j.val := by
          simp only [copies,List.length_map,List.length_finRange,Fin.val_succ,Nat.add_mul,Nat.one_mul]
          omega
        simp only [he]
        exact ih k
end PlanarHom.ParallelSource
