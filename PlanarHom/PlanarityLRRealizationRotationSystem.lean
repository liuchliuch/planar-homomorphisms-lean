import PlanarHom.PlanarityLRRowIncidence
import PlanarHom.PlanarityLRRealizationGermPieces
import Mathlib.GroupTheory.Perm.List

/-! NEW exact typed rotation system of the deterministic occurrence LR rows.
This closes incidence and permutation semantics; geometric realization remains
separate and is never a field of the computed row data. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*}

structure RotationRows (G : MultiGraph V E) [DecidableEq (Dart E)] where
  row : V → List (Dart E)
  nodup : ∀ v, (row v).Nodup
  mem : ∀ v a, a ∈ row v ↔ (G.dartPair a).1 = v

namespace RotationRows
variable {G : MultiGraph V E} [DecidableEq (Dart E)] (R : RotationRows G)

theorem next_host (a : Dart E) :
    (G.dartPair ((R.row (G.dartPair a).1).formPerm a)).1 = (G.dartPair a).1 :=
  (R.mem _ _).mp (List.formPerm_apply_mem_of_mem ((R.mem _ a).mpr rfl))

theorem prev_host (a : Dart E) :
    (G.dartPair ((R.row (G.dartPair a).1).formPerm.symm a)).1 = (G.dartPair a).1 := by
  apply (R.mem _ _).mp
  apply List.mem_of_formPerm_apply_mem
  simpa using (R.mem _ a).mpr rfl

/-- The exact row-cycle permutation, with explicit inverse in the same host row. -/
def rotation : Equiv.Perm (Dart E) where
  toFun a := (R.row (G.dartPair a).1).formPerm a
  invFun a := (R.row (G.dartPair a).1).formPerm.symm a
  left_inv a := by
    dsimp only
    rw [R.next_host]
    exact Equiv.symm_apply_apply _ a
  right_inv a := by
    dsimp only
    rw [R.prev_host]
    exact Equiv.apply_symm_apply _ a

@[simp] theorem rotation_apply (a : Dart E) : R.rotation a = (R.row (G.dartPair a).1).formPerm a := rfl
@[simp] theorem rotation_host (a : Dart E) : (G.dartPair (R.rotation a)).1 = (G.dartPair a).1 := R.next_host a
end RotationRows

/-- Mapping an injectively named row commutes with its exact cyclic permutation. -/
theorem map_formPerm_apply {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (hn : xs.Nodup) {a : A} (ha : a ∈ xs) :
    (xs.map f).formPerm (f a) = f (xs.formPerm a) := by
  obtain ⟨i,hi,hget⟩ := List.mem_iff_getElem.mp ha
  rw [← hget]
  have hm := List.formPerm_apply_getElem (xs.map f) (hn.map hf) i (by simpa using hi)
  simpa only [List.getElem_map,List.length_map,List.formPerm_apply_getElem xs hn i hi] using hm

open Complexity PlanarityLRDirect

/-- Erase only the finite proof, retaining the literal edge index and dart direction. -/
def eraseDart {g : MixedCode} (a : Dart (Fin g.edges.length)) : PlanarityRotationCode.Dart := (a.1.val,a.2)

def liftDart {g : MixedCode} (a : PlanarityRotationCode.Dart) (ha : a.1 < g.edges.length) :
    Dart (Fin g.edges.length) := (⟨a.1,ha⟩,a.2)

@[simp] theorem erase_liftDart {g : MixedCode} (a : PlanarityRotationCode.Dart) (ha : a.1 < g.edges.length) :
    eraseDart (g := g) (liftDart a ha) = a := by cases a; rfl

theorem eraseDart_injective (g : MixedCode) : Function.Injective (eraseDart (g := g)) := by
  intro a b h
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst h)
  · exact congrArg (fun x : PlanarityRotationCode.Dart => x.2) h

theorem eraseDart_host (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (a : Dart (Fin g.edges.length)) :
    PlanarityRotationCode.host g (eraseDart a) = ((g.toMultiGraph hg).dartPair a).1.val := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [PlanarityRotationCode.host,eraseDart,PlanarityLRRawConstraints.edge,
    dartPair,MixedCode.toMultiGraph,List.getD_eq_getElem?_getD,e.isLt,List.get_eq_getElem]

def typedDirectRow (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (v : Fin g.vertices) : List (Dart (Fin g.edges.length)) :=
  (directRow g bits v.val).attach.map (fun a => liftDart a.val ((mem_directRow g hg bits v.isLt a.val).mp a.property).1)

theorem erase_typedDirectRow (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (v : Fin g.vertices) : (typedDirectRow g hg bits v).map eraseDart = directRow g bits v.val := by
  simp [typedDirectRow,List.map_map,Function.comp_def,List.attach_map_subtype_val]

theorem typedDirectRow_nodup (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (v : Fin g.vertices) : (typedDirectRow g hg bits v).Nodup := by
  apply List.Nodup.of_map eraseDart
  rw [erase_typedDirectRow]
  exact directRow_nodup g hg bits v.isLt

theorem mem_typedDirectRow_iff_erase (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (v : Fin g.vertices) (a : Dart (Fin g.edges.length)) :
    a ∈ typedDirectRow g hg bits v ↔ eraseDart a ∈ directRow g bits v.val := by
  rw [← erase_typedDirectRow g hg bits v]
  constructor
  · exact fun h => List.mem_map.mpr ⟨a,h,rfl⟩
  · intro h
    obtain ⟨b,hb,he⟩ := List.mem_map.mp h
    exact eraseDart_injective g he ▸ hb

theorem mem_typedDirectRow (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (v : Fin g.vertices) (a : Dart (Fin g.edges.length)) :
    a ∈ typedDirectRow g hg bits v ↔ ((g.toMultiGraph hg).dartPair a).1 = v := by
  rw [mem_typedDirectRow_iff_erase,mem_directRow g hg bits v.isLt,eraseDart_host]
  simp only [eraseDart,a.1.isLt,true_and]
  exact Fin.val_inj

/-- Actual computed rows, with all incidence obligations proved from raw validity. -/
def directRotationRows (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool) :
    RotationRows (g.toMultiGraph hg) where
  row := typedDirectRow g hg bits
  nodup := typedDirectRow_nodup g hg bits
  mem := mem_typedDirectRow g hg bits

theorem typedDirectRow_formPerm_erase (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (v : Fin g.vertices) {a : Dart (Fin g.edges.length)} (ha : a ∈ typedDirectRow g hg bits v) :
    eraseDart ((typedDirectRow g hg bits v).formPerm a) =
      (directRow g bits v.val).formPerm (eraseDart a) := by
  have h := map_formPerm_apply eraseDart (eraseDart_injective g) _ (typedDirectRow_nodup g hg bits v) ha
  rw [erase_typedDirectRow] at h
  exact h.symm

theorem rowNext_eq_formPerm (row : List PlanarityRotationCode.Dart) (hn : row.Nodup)
    (a : PlanarityRotationCode.Dart) (ha : a ∈ row) : rowNext row a = row.formPerm a := by
  have hi : row.idxOf a < row.length := List.idxOf_lt_length_iff.mpr ha
  have hm : (row.idxOf a+1)%row.length < row.length := Nat.mod_lt _ (by omega)
  have he : row[row.idxOf a] = a := by
    exact eq_of_beq (List.findIdx_getElem (xs := row) (p := fun b => b == a) (w := hi))
  have hp := List.formPerm_apply_getElem row hn (row.idxOf a) hi
  rw [he] at hp
  rw [rowNext,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hm,Option.getD_some]
  exact hp.symm

/-- The typed permutation is exactly the raw executable rotation, not a chosen
permutation supplied independently of the program. -/
theorem directRotationRows_erase (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    eraseDart ((directRotationRows g hg bits).rotation a) =
      directRotation g bits (eraseDart a) := by
  let v := ((g.toMultiGraph hg).dartPair a).1
  change eraseDart ((typedDirectRow g hg bits v).formPerm a) = _
  rw [typedDirectRow_formPerm_erase g hg bits v ((mem_typedDirectRow g hg bits v a).mpr rfl)]
  unfold directRotation
  rw [eraseDart_host g hg a]
  symm
  apply rowNext_eq_formPerm _ (directRow_nodup g hg bits v.isLt)
  exact (mem_typedDirectRow_iff_erase g hg bits v a).mp ((mem_typedDirectRow g hg bits v a).mpr rfl)

end PlanarHom.PlanarityLRRealization
