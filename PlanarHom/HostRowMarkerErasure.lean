import PlanarHom.ListRotationRemoveNone

/-! Exact removal of an arbitrary finite set of markers from a complete family
of cyclic vertex rows. Rows containing only deleted markers disappear without
adding a visible fixed point; the retained linear rows are literal filters. -/
noncomputable section
open Classical
namespace PlanarHom
open Equiv FinitePermutationCycles

structure HostRowSystem (V D : Type) where
  host : D → V
  row : V → List D
  nodup : ∀v,(row v).Nodup
  mem : ∀v a,a∈row v ↔ host a=v

namespace HostRowSystem
variable {V D A B : Type} [DecidableEq D] [DecidableEq A] [DecidableEq B]

theorem next_host (F : HostRowSystem V D) (a : D) :
    F.host ((F.row (F.host a)).formPerm a)=F.host a :=
  (F.mem _ _).mp (List.formPerm_apply_mem_of_mem ((F.mem _ _).mpr rfl))

theorem prev_host (F : HostRowSystem V D) (a : D) :
    F.host ((F.row (F.host a)).formPerm.symm a)=F.host a := by
  apply (F.mem _ _).mp
  apply List.mem_of_formPerm_apply_mem
  simpa using (F.mem _ a).mpr rfl

def rotation (F : HostRowSystem V D) : Equiv.Perm D where
  toFun a := (F.row (F.host a)).formPerm a
  invFun a := (F.row (F.host a)).formPerm.symm a
  left_inv a := by
    dsimp only
    rw [F.next_host]
    exact Equiv.symm_apply_apply _ a
  right_inv a := by
    dsimp only
    rw [F.prev_host]
    exact Equiv.apply_symm_apply _ a

def relabel (F : HostRowSystem V A) (e : A≃B) : HostRowSystem V B where
  host b := F.host (e.symm b)
  row v := (F.row v).map e
  nodup v := (F.nodup v).map e.injective
  mem v b := by
    constructor
    · intro hb
      obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hb
      simpa using (F.mem _ _).mp ha
    · intro hb
      exact List.mem_map.mpr ⟨e.symm b,(F.mem _ _).mpr hb,e.apply_symm_apply b⟩

theorem relabel_rotation (F : HostRowSystem V A) (e : A≃B) :
    (F.relabel e).rotation=e.permCongr F.rotation := by
  apply Equiv.ext
  intro b
  change ((F.row (F.host (e.symm b))).map e).formPerm b=e ((F.row (F.host (e.symm b))).formPerm (e.symm b))
  have h:=PlanarityLRRealization.map_formPerm_apply e e.injective (F.row (F.host (e.symm b)))
    (F.nodup _) ((F.mem _ _).mpr rfl)
  simpa only [e.apply_symm_apply] using h

def eraseNone (F : HostRowSystem V (Option A)) : HostRowSystem V A where
  host a := F.host (some a)
  row v := (F.row v).filterMap id
  nodup v := ListRotationErasure.filterSome_nodup _ (F.nodup v)
  mem v a := (ListRotationErasure.mem_filterSome _ _).trans (F.mem _ _)

theorem eraseNone_rotation (F : HostRowSystem V (Option A)) :
    F.eraseNone.rotation=Equiv.removeNone F.rotation := by
  apply Equiv.ext
  intro a
  change ((F.row (F.host (some a))).filterMap id).formPerm a=(Equiv.removeNone F.rotation) a
  rw [←ListRotationErasure.removeNone_formPerm _ (F.nodup _)]
  apply Option.some_injective
  by_cases hr : F.rotation (some a)=none
  · have hl : (F.row (F.host (some a))).formPerm (some a)=none := hr
    rw [Equiv.removeNone_none _ hl,Equiv.removeNone_none _ hr]
    have hh:=F.next_host (some a)
    change F.host (F.rotation (some a))=F.host (some a) at hh
    rw [hr] at hh
    change _=(F.row (F.host none)).formPerm none
    rw [hh]
  · cases he : F.rotation (some a) with
    | none => exact False.elim (hr he)
    | some b =>
      have hl : (F.row (F.host (some a))).formPerm (some a)=some b := he
      rw [Equiv.removeNone_some _ ⟨b,hl⟩,Equiv.removeNone_some _ ⟨b,he⟩]
      rfl

variable [Fintype A]

def keepLeft {X : Type} : A⊕X → Option A
  | .inl a => some a
  | .inr _ => none

def eraseMarkers : {n : ℕ} → HostRowSystem V (A⊕Fin n) → HostRowSystem V A
  | 0,F => F.relabel (Equiv.sumEmpty A (Fin 0))
  | n+1,F => eraseMarkers ((F.relabel (markerOptionEquiv n)).eraseNone)

theorem eraseMarkers_rotation (n : ℕ) (F : HostRowSystem V (A⊕Fin n)) :
    (eraseMarkers F).rotation=eraseFinMarkers F.rotation := by
  induction n with
  | zero => exact relabel_rotation F _
  | succ n ih =>
    change (eraseMarkers ((F.relabel (markerOptionEquiv n)).eraseNone)).rotation=_
    rw [ih,eraseNone_rotation,relabel_rotation]
    rfl

theorem eraseMarkers_host (n : ℕ) (F : HostRowSystem V (A⊕Fin n)) (a : A) :
    (eraseMarkers F).host a=F.host (.inl a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (eraseMarkers ((F.relabel (markerOptionEquiv n)).eraseNone)).host a=_
    rw [ih]
    rfl

theorem eraseMarkers_row (n : ℕ) (F : HostRowSystem V (A⊕Fin n)) (v : V) :
    (eraseMarkers F).row v=(F.row v).filterMap keepLeft := by
  induction n with
  | zero =>
    change (F.row v).map (Equiv.sumEmpty A (Fin 0))=_
    have he : (keepLeft : A⊕Fin 0→Option A)=some ∘ Equiv.sumEmpty A (Fin 0) := by
      funext x
      cases x with
      | inl a => rfl
      | inr i => exact i.elim0
    rw [he,List.filterMap_eq_map]
  | succ n ih =>
    change (eraseMarkers ((F.relabel (markerOptionEquiv n)).eraseNone)).row v=_
    rw [ih]
    change (((F.row v).map (markerOptionEquiv n)).filterMap id).filterMap keepLeft=_
    rw [List.filterMap_filterMap,List.filterMap_map]
    apply List.filterMap_congr
    intro x _
    cases x with
    | inl a => rfl
    | inr j => exact Fin.cases rfl (fun _=>rfl) j

/-- The canonical finite marker erasure acts exactly as the cyclic permutation
of the retained row at every original dart. -/
theorem eraseFinMarkers_apply (n : ℕ) (F : HostRowSystem V (A⊕Fin n)) (a : A) :
    eraseFinMarkers F.rotation a=((F.row (F.host (.inl a))).filterMap keepLeft).formPerm a := by
  rw [←eraseMarkers_rotation]
  change ((eraseMarkers F).row ((eraseMarkers F).host a)).formPerm a=_
  rw [eraseMarkers_host,eraseMarkers_row]

theorem eraseFinMarkers_eq_of_rows (n : ℕ) (F : HostRowSystem V (A⊕Fin n)) (P : Equiv.Perm A)
    (h : ∀a,((F.row (F.host (.inl a))).filterMap keepLeft).formPerm a=P a) :
    eraseFinMarkers F.rotation=P := by
  apply Equiv.ext
  intro a
  rw [eraseFinMarkers_apply]
  exact h a

end HostRowSystem
end PlanarHom
