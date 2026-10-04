import PlanarHom.ParallelSourceRowPositions

/-! Literal successor formulas for inherited parallel-copy rotations. -/
noncomputable section
open Classical
namespace PlanarHom.ParallelSource
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {E : Type} [DecidableEq (Dart E)]

 theorem expand_formPerm_inner {t : ℕ} (xs : List (Dart E)) (hn : xs.Nodup)
    (i : Fin xs.length) (j : Fin t) (hj : j.val+1<t) :
    (expand t xs).formPerm (copyDart (xs.get i) j)=copyDart (xs.get i) ⟨j.val+1,hj⟩ := by
  rw [←expand_get xs i j,List.formPerm_apply_getElem _ (expand_nodup t xs hn)]
  have hb : i.val*t+j.val+1<(expand t xs).length := by
    rw [expand_length]
    have hi := i.isLt
    nlinarith
  simp only [Nat.mod_eq_of_lt hb]
  have he : i.val*t+j.val+1=i.val*t+(j.val+1) := by omega
  simp only [he]
  exact expand_get xs i ⟨j.val+1,hj⟩

 theorem expand_formPerm_last (n : ℕ) (xs : List (Dart E)) (hn : xs.Nodup)
    (i : Fin xs.length) :
    (expand (n+1) xs).formPerm (copyDart (xs.get i) (Fin.last n))=
      copyDart (xs.formPerm (xs.get i)) (0 : Fin (n+1)) := by
  have hl : 0<xs.length := Nat.zero_lt_of_lt i.isLt
  rw [←expand_get xs i (Fin.last n),List.formPerm_apply_getElem _ (expand_nodup (n+1) xs hn)]
  have hnext : (i.val+1)%xs.length<xs.length := Nat.mod_lt _ hl
  have he : (i.val*(n+1)+(Fin.last n).val+1)%(expand (n+1) xs).length=
      ((i.val+1)%xs.length)*(n+1)+(0 : Fin (n+1)).val := by
    rw [expand_length]
    simp only [Fin.val_last,Fin.val_zero,Nat.add_zero]
    have hp : i.val*(n+1)+n+1=(i.val+1)*(n+1) := by ring
    rw [hp]
    by_cases hi : i.val+1<xs.length
    · rw [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (by nlinarith : (i.val+1)*(n+1)<xs.length*(n+1))]
    · have hie : i.val+1=xs.length := by have := i.isLt; omega
      rw [hie,Nat.mod_self,Nat.mod_self,Nat.zero_mul]
  simp only [he]
  rw [expand_get xs ⟨(i.val+1)%xs.length,hnext⟩ (0 : Fin (n+1))]
  apply congrArg (fun a => copyDart a (0 : Fin (n+1)))
  symm
  exact List.formPerm_apply_getElem xs hn i.val i.isLt

variable {V : Type} {G : MultiGraph V E}

 theorem rotation_inner (R : RotationRows G) {t : ℕ} (a : Dart E) (j : Fin t) (hj : j.val+1<t) :
    (rows R t).rotation (copyDart a j)=copyDart a ⟨j.val+1,hj⟩ := by
  have ha : a∈R.row (G.dartPair a).1 := (R.mem _ a).mpr rfl
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp ha
  have hh := expand_formPerm_inner (R.row (G.dartPair a).1) (R.nodup _) ⟨i,hi⟩ j hj
  change (expand t (R.row (G.dartPair a).1)).formPerm (copyDart a j)=_
  simpa only [List.get_eq_getElem,he] using hh

 theorem rotation_last (R : RotationRows G) (n : ℕ) (a : Dart E) :
    (rows R (n+1)).rotation (copyDart a (Fin.last n))=
      copyDart (R.rotation a) (0 : Fin (n+1)) := by
  have ha : a∈R.row (G.dartPair a).1 := (R.mem _ a).mpr rfl
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp ha
  have hh := expand_formPerm_last n (R.row (G.dartPair a).1) (R.nodup _) ⟨i,hi⟩
  change (expand (n+1) (R.row (G.dartPair a).1)).formPerm (copyDart a (Fin.last n))=
    copyDart ((R.row (G.dartPair a).1).formPerm a) (0 : Fin (n+1))
  simpa only [List.get_eq_getElem,he] using hh
end PlanarHom.ParallelSource
