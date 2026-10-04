import PlanarHom.PlanarProperLocalizedCollapse

/-! NEW composition API for actual proper single-fiber plane collapses. The
segment and finite-tree existence theorems construct all fields geometrically. -/
noncomputable section
open Set Topology
namespace PlanarHom.MultiGraph

structure ProperPlaneCollapse (S : Set Plane) (c : Plane) where
  map : C(Plane,Plane)
  proper : IsProperMap map
  onto : Function.Surjective map
  fibers : ∀ x y, map x = map y ↔ x=y ∨ (x∈S ∧ y∈S)
  center_mem : c ∈ S
  center_fixed : map c = c

namespace ProperPlaneCollapse
variable {S T : Set Plane} {c d : Plane}

@[simp] theorem map_on_support (C : ProperPlaneCollapse S c) {x : Plane} (hx : x∈S) :
    C.map x = c := ((C.fibers x c).mpr (Or.inr ⟨hx,C.center_mem⟩)).trans C.center_fixed

theorem map_eq_center_iff (C : ProperPlaneCollapse S c) (x : Plane) : C.map x = c ↔ x∈S := by
  constructor
  · intro h
    rcases (C.fibers x c).mp (h.trans C.center_fixed.symm) with heq | hmem
    · exact heq ▸ C.center_mem
    · exact hmem.1
  · exact C.map_on_support

/-- Every constructed proper collapse has the exact expected ambient complement
homeomorphism, using a closed bijection rather than invariance of domain. -/
def complementHomeomorph (C : ProperPlaneCollapse S c) :
    {x : Plane // x∉S} ≃ₜ {y : Plane // y≠c} := by
  let U : Set Plane := {y | y≠c}
  let f := U.restrictPreimage C.map
  have hinj : Function.Injective f := by
    intro x y h
    rcases (C.fibers x.val y.val).mp (congrArg Subtype.val h) with heq | hmem
    · exact Subtype.ext heq
    · exact False.elim (x.property (C.map_on_support hmem.1))
  have hsur : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := C.onto y.val
    refine ⟨⟨x,?_⟩,Subtype.ext hx⟩
    change C.map x ≠ c
    rw [hx]
    exact y.property
  let H := (Equiv.ofBijective f ⟨hinj,hsur⟩).toHomeomorphOfContinuousClosed
    C.map.continuous.restrictPreimage (C.proper.isClosedMap.restrictPreimage U)
  have hS : {x : Plane | x∉S} = C.map ⁻¹' U := by
    ext x
    exact (not_congr (C.map_eq_center_iff x)).symm
  exact (Homeomorph.setCongr hS).trans H

@[simp] theorem complementHomeomorph_apply (C : ProperPlaneCollapse S c)
    (x : {x : Plane // x∉S}) : (C.complementHomeomorph x : Plane) = C.map x := rfl

/-- The identity collapses a singleton, with no exceptional non-singleton fiber. -/
def singleton (c : Plane) : ProperPlaneCollapse {c} c where
  map := ContinuousMap.id Plane
  proper := isProperMap_id
  onto := Function.surjective_id
  fibers x y := by
    simp only [ContinuousMap.id_apply,Set.mem_singleton_iff]
    constructor
    · exact Or.inl
    · rintro (h | ⟨hx,hy⟩)
      · exact h
      · exact hx.trans hy.symm
  center_mem := rfl
  center_fixed := rfl

/-- Compose a leaf collapse with the retained-tree collapse. The exact invariant
is that the first map preserves the retained support as a set and its root. -/
def merge (C : ProperPlaneCollapse S c) (D : ProperPlaneCollapse T d)
    (hc : c∈T) (hT : C.map '' T = T) (hd : C.map d = d) :
    ProperPlaneCollapse (S∪T) d where
  map := D.map.comp C.map
  proper := D.proper.comp C.proper
  onto := D.onto.comp C.onto
  fibers := by
    have hpre (x : Plane) : C.map x ∈ T ↔ x∈S∪T := by
      constructor
      · intro hx
        obtain ⟨y,hy,hyx⟩ := (show C.map x ∈ C.map '' T by rw [hT]; exact hx)
        rcases (C.fibers y x).mp hyx with heq | hmem
        · exact Or.inr (heq ▸ hy)
        · exact Or.inl hmem.2
      · rintro (hx | hx)
        · rwa [C.map_on_support hx]
        · rw [← hT]
          exact ⟨x,hx,rfl⟩
    intro x y
    change D.map (C.map x) = D.map (C.map y) ↔ _
    rw [D.fibers]
    constructor
    · rintro (heq | hmem)
      · rcases (C.fibers x y).mp heq with heq | hmem
        · exact Or.inl heq
        · exact Or.inr ⟨Or.inl hmem.1,Or.inl hmem.2⟩
      · exact Or.inr ⟨(hpre x).mp hmem.1,(hpre y).mp hmem.2⟩
    · rintro (rfl | hmem)
      · exact Or.inl rfl
      · exact Or.inr ⟨(hpre x).mpr hmem.1,(hpre y).mpr hmem.2⟩
  center_mem := Or.inr D.center_mem
  center_fixed := by change D.map (C.map d) = d; rw [hd,D.center_fixed]

@[simp] theorem merge_apply (C : ProperPlaneCollapse S c) (D : ProperPlaneCollapse T d)
    (hc : c∈T) (hT : C.map '' T = T) (hd : C.map d = d) (x : Plane) :
    (C.merge D hc hT hd).map x = D.map (C.map x) := rfl

end ProperPlaneCollapse
end PlanarHom.MultiGraph
