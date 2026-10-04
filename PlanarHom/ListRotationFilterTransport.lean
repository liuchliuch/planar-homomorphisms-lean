import PlanarHom.ListRotationRemoveNone

noncomputable section
open Classical
namespace PlanarHom.ListRotationErasure
variable {A B : Type} [DecidableEq A] [DecidableEq B]

theorem filterMap_nodup (f : A→Option B)
    (hf : ∀a b y,f a=some y→f b=some y→a=b) (xs : List A) (h : xs.Nodup) :
    (xs.filterMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases he : f a with
    | none => simpa only [List.filterMap_cons,he] using ih h.of_cons
    | some b =>
      simp only [List.filterMap_cons,he,List.nodup_cons]
      refine ⟨?_,ih h.of_cons⟩
      intro hb
      obtain ⟨x,hx,hfx⟩:=List.mem_filterMap.mp hb
      exact h.notMem ((hf a x b he hfx).symm ▸ hx)

theorem filterMap_isRotated (f : A→Option B) {xs ys : List A} (h : xs ~r ys) :
    xs.filterMap f ~r ys.filterMap f := by
  obtain ⟨n,rfl⟩:=h
  let k:=n%xs.length
  have hr : xs.rotate n=xs.drop k++xs.take k := List.rotate_eq_drop_append_take_mod
  rw [hr,List.filterMap_append]
  have hx : xs.filterMap f=(xs.take k).filterMap f++(xs.drop k).filterMap f := by
    rw [←List.filterMap_append,List.take_append_drop]
  rw [hx]
  exact List.isRotated_append

/-- Equal cyclic permutations remain equal after deleting elements through an
injective partial renaming. Short/empty rows are handled without a support or
nonemptiness assumption. -/
theorem filterMap_formPerm_eq (f : A→Option B)
    (hf : ∀a b y,f a=some y→f b=some y→a=b)
    (xs ys : List A) (hx : xs.Nodup) (hy : ys.Nodup) (hp : xs.formPerm=ys.formPerm) :
    (xs.filterMap f).formPerm=(ys.filterMap f).formPerm := by
  have hfx:=filterMap_nodup f hf xs hx
  have hfy:=filterMap_nodup f hf ys hy
  rcases (List.formPerm_eq_formPerm_iff hx hy).mp hp with h | ⟨hxs,hys⟩
  · exact List.formPerm_eq_of_isRotated hfx (filterMap_isRotated f h)
  · rw [(List.formPerm_eq_one_iff _ hfx).mpr ((List.length_filterMap_le f xs).trans hxs),
      (List.formPerm_eq_one_iff _ hfy).mpr ((List.length_filterMap_le f ys).trans hys)]

theorem formPerm_map_apply (f : A→B) (hf : Function.Injective f) (xs : List A) (a : A) :
    (xs.map f).formPerm (f a)=f (xs.formPerm a) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simp only [List.map_cons,List.formPerm_cons_cons,Equiv.Perm.mul_apply]
      have ih' : (f y::ys.map f).formPerm (f a)=f ((y::ys).formPerm a) := ih
      rw [ih']
      simp only [Equiv.swap_apply_def,hf.eq_iff]
      split_ifs <;> rfl

end PlanarHom.ListRotationErasure
