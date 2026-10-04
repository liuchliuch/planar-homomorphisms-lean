import PlanarHom.PlanarityLRContourPermutation
import PlanarHom.PlanarRibbons

/-! Inherited clockwise rows of literal parallel edge copies. Source ends
list copies increasingly, target ends decreasingly, while the source row
order is preserved. This is the same convention as the raw serializer. -/
noncomputable section
open Classical
namespace PlanarHom.ParallelSource
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type} {G : MultiGraph V E}

 def baseDart {t : ℕ} (a : Dart (E×Fin t)) : Dart E := (a.1.1,a.2)
 def orientedIndex {t : ℕ} (forward : Bool) (i : Fin t) : Fin t := if forward then i else i.rev

 @[simp] theorem orientedIndex_twice {t : ℕ} (b : Bool) (i : Fin t) :
    orientedIndex b (orientedIndex b i)=i := by cases b <;> simp [orientedIndex]

 theorem orientedIndex_injective {t : ℕ} (b : Bool) : Function.Injective (orientedIndex (t:=t) b) :=
  Function.LeftInverse.injective (orientedIndex_twice b)

 def copyDart {t : ℕ} (a : Dart E) (i : Fin t) : Dart (E×Fin t) :=
  ((a.1,orientedIndex a.2 i),a.2)

 @[simp] theorem base_copy {t : ℕ} (a : Dart E) (i : Fin t) : baseDart (copyDart a i)=a := by cases a; rfl

 theorem copyDart_injective {t : ℕ} (a : Dart E) : Function.Injective (copyDart (t:=t) a) := by
  intro i j h
  exact orientedIndex_injective a.2 (congrArg (fun d => d.1.2) h)

 def copies (t : ℕ) (a : Dart E) : List (Dart (E×Fin t)) := (List.finRange t).map (copyDart a)

 theorem mem_copies (t : ℕ) (a : Dart E) (b : Dart (E×Fin t)) :
    b∈copies t a ↔ baseDart b=a := by
  constructor
  · intro h
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    exact base_copy a i
  · intro h
    subst a
    refine List.mem_map.mpr ⟨orientedIndex b.2 b.1.2,List.mem_finRange _,?_⟩
    rcases b with ⟨⟨e,i⟩,b⟩
    simp [copyDart,baseDart]

 theorem copies_nodup (t : ℕ) (a : Dart E) : (copies t a).Nodup :=
  (List.nodup_finRange t).map (copyDart_injective a)

 theorem copies_disjoint (t : ℕ) (a b : Dart E) (h : a≠b) :
    List.Disjoint (copies t a) (copies t b) := by
  intro x hx hy
  exact h ((mem_copies t a x).mp hx |>.symm.trans ((mem_copies t b x).mp hy))

 def expand (t : ℕ) (xs : List (Dart E)) : List (Dart (E×Fin t)) := xs.flatMap (copies t)

 theorem expand_nodup (t : ℕ) (xs : List (Dart E)) (h : xs.Nodup) : (expand t xs).Nodup := by
  apply List.nodup_flatMap.mpr
  exact ⟨fun a _ => copies_nodup t a,h.imp (fun hne => copies_disjoint t _ _ hne)⟩

 theorem mem_expand (t : ℕ) (xs : List (Dart E)) (a : Dart (E×Fin t)) :
    a∈expand t xs ↔ baseDart a∈xs := by
  simp only [expand,List.mem_flatMap,mem_copies]
  constructor
  · rintro ⟨b,hb,he⟩; simpa [he] using hb
  · intro h; exact ⟨baseDart a,h,rfl⟩

 theorem thicken_host (t : ℕ) (a : Dart (E×Fin t)) :
    ((G.thicken t).dartPair a).1=(G.dartPair (baseDart a)).1 := by
  rcases a with ⟨⟨e,i⟩,b⟩
  cases b <;> rfl

 def rows [DecidableEq (Dart E)] (R : RotationRows G) (t : ℕ) : RotationRows (G.thicken t) where
  row v := expand t (R.row v)
  nodup v := expand_nodup t _ (R.nodup v)
  mem v a := by rw [mem_expand,R.mem,thicken_host]

 theorem row_length [DecidableEq (Dart E)] (R : RotationRows G) (t : ℕ) (v : V) :
    ((rows R t).row v).length=(R.row v).length*t := by
  change (expand t (R.row v)).length=_
  generalize R.row v=xs
  induction xs with
  | nil => simp [expand]
  | cons a xs ih =>
      change (copies t a++expand t xs).length=(xs.length+1)*t
      rw [List.length_append,ih]
      simp [copies,Nat.add_mul,Nat.add_comm]
end PlanarHom.ParallelSource
