import PlanarHom.PlanarColoringClausePortSemantics

/-! An unpinned, equivariant interface for the actual nine-port clause.  The
palette is recovered from boundary vertices; it is part of the coloring state,
not an external assumption or a quotient of the solution count. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarColoringClause
open ThreeColorPaletteCounting ParsimoniousNorOneInThree
set_option maxHeartbeats 5000000

abbrev PaletteState := Palette × Accepted

def palettePermutation (p : Palette) : Equiv.Perm (Fin 3) :=
  paletteEquiv p.val.1 p.val.2 p.property

def stateExtension (s : PaletteState) : Fin 9 ⊕ InternalVertex → Fin 3 :=
  palettePermutation s.1 ∘ patchExtension s.2.val

def statePort (s : PaletteState) : Fin 9 → Fin 3 :=
  palettePermutation s.1 ∘ portColor s.2.val

@[simp] theorem stateExtension_port (s : PaletteState) (k : Fin 9) :
    stateExtension s (.inl k)=statePort s k := by
  simp [stateExtension,statePort]

@[simp] theorem statePort_black (s : PaletteState) (k : Fin 3) :
    statePort s (blackPort k)=s.1.val.1 := by
  fin_cases k <;> rfl

@[simp] theorem statePort_gray (s : PaletteState) (k : Fin 3) :
    statePort s (grayPort k)=s.1.val.2 := by
  fin_cases k <;> rfl

@[simp] theorem statePort_primary (s : PaletteState) (k : Fin 3) :
    statePort s (primaryPort k)=palettePermutation s.1 (boolColor (s.2.val k)) := by
  simp only [statePort,Function.comp_apply,portColor_primary]

theorem stateExtension_proper (s : PaletteState) : PatchProper (stateExtension s) := by
  have h := ((patch_spec_iff (patchExtension s.2.val) s.2.val).mpr ⟨s.2.property,rfl⟩).1
  intro e
  exact fun he => h e ((palettePermutation s.1).injective he)

/-- A proper clause forces a distinct palette pair on its actual boundary. -/
theorem patch_boundary_separated (col : Fin 9 ⊕ InternalVertex → Fin 3)
    (h : PatchProper col) : col (.inl 1)≠col (.inl 2) := by
  have hp := (patchProper_iff col).mp h
  have hs := (proper_split (col ∘ labels.symm)).mp hp
  have hc := PlanarColoringOneWayConverter.palette_copy ((col ∘ labels.symm) ∘ copyVertex 0) (hs.1 0)
  have hw := (PlanarColoringExclusiveCrossing.proper_iff _).mp (hs.2.1 0)
  have hb : (col ∘ labels.symm) (copyVertex 0 2)=col (.inl 1) := by
    change col (labels.symm (boundary 1))=_
    rw [labels_symm_boundary]
  have hg : (col ∘ labels.symm) (copyVertex 1 6)=col (.inl 2) := by
    change col (labels.symm (boundary 2))=_
    rw [labels_symm_boundary]
  have hgg : (col ∘ labels.symm) (copyVertex 1 6)=(col ∘ labels.symm) (copyVertex 0 4) := congrFun hw.2 3
  rw [← hb,← hg,hgg]
  exact hc.1.symm ▸ hc.2.1.symm ▸ hc.2.2

/-- Complete reconstruction from a proper coloring, allowing every labeled
palette permutation rather than silently pinning the graph. -/
theorem exists_state (col : Fin 9 ⊕ InternalVertex → Fin 3) (h : PatchProper col) :
    ∃ s : PaletteState,col=stateExtension s := by
  let p : Palette := ⟨(col (.inl 1),col (.inl 2)),patch_boundary_separated col h⟩
  let normal := (palettePermutation p).symm ∘ col
  have hn : PatchProper normal := by
    intro e he
    exact h e ((palettePermutation p).symm.injective he)
  have hnb : normal (.inl 1)=0 := by
    exact (palettePermutation p).symm_apply_eq.mpr rfl
  have hng : normal (.inl 2)=1 := by
    exact (palettePermutation p).symm_apply_eq.mpr rfl
  have hp := (patchProper_iff normal).mp hn
  have hh := (boundary_pinned_iff (normal ∘ labels.symm)).mp ⟨hp,by simpa only [Function.comp_apply,labels_symm_boundary] using hnb,
    by simpa only [Function.comp_apply,labels_symm_boundary] using hng⟩
  let b := inputBits (normal ∘ labels.symm)
  refine ⟨(p,⟨b,hh.1⟩),?_⟩
  funext v
  have he := congrFun hh.2 (labels v)
  simp only [Function.comp_apply,Equiv.symm_apply_apply] at he
  change col v=palettePermutation p (extension b (labels v))
  rw [←he]
  exact ((palettePermutation p).apply_symm_apply (col v)).symm

theorem boolColor_injective : Function.Injective boolColor := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolColor]

/-- All state coordinates are determined by the exposed ports. -/
theorem statePort_injective : Function.Injective statePort := by
  rintro ⟨p,b⟩ ⟨q,c⟩ h
  have hb := congrFun h (blackPort 0)
  have hg := congrFun h (grayPort 0)
  simp only [statePort_black,statePort_gray] at hb hg
  have hp : p=q := Subtype.ext (Prod.ext hb hg)
  subst q
  have hc : b=c := by
    apply Subtype.ext
    funext k
    have hk := congrFun h (primaryPort k)
    simp only [statePort_primary] at hk
    exact boolColor_injective ((palettePermutation p).injective hk)
  subst c
  rfl

theorem stateExtension_injective : Function.Injective stateExtension := by
  intro s t h
  apply statePort_injective
  funext k
  simpa only [stateExtension_port] using congrFun h (.inl k)

/-- The ordinary colorings of the literal clause patch are precisely its
palette together with its satisfying Boolean triple. -/
def patchStateEquiv : {col : Fin 9 ⊕ InternalVertex → Fin 3 // PatchProper col} ≃ PaletteState :=
  (Equiv.ofBijective
    (fun s : PaletteState => (⟨stateExtension s,stateExtension_proper s⟩ :
      {col : Fin 9 ⊕ InternalVertex → Fin 3 // PatchProper col}))
    ⟨fun s t h => stateExtension_injective (congrArg Subtype.val h),by
      intro col
      obtain ⟨s,hs⟩ := exists_state col.val col.property
      exact ⟨s,Subtype.ext hs.symm⟩⟩).symm

end PlanarHom.PlanarColoringClause
