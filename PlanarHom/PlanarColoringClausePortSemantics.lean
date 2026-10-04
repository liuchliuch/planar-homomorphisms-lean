import PlanarHom.PlanarColoringClausePorts
import PlanarHom.PlanarColoringClauseCounting

/-! Direct nine-port semantics of the geometrically certified exact-one patch.
Primary ports are 0,3,6; the intervening pairs are black/gray palette ports. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarColoringClause
open ParsimoniousNorOneInThree
set_option maxHeartbeats 5000000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 20000

def primaryPort (k : Fin 3) : Fin 9 := ⟨3*k.val,by omega⟩
def blackPort (k : Fin 3) : Fin 9 := ⟨3*k.val+1,by omega⟩
def grayPort (k : Fin 3) : Fin 9 := ⟨3*k.val+2,by omega⟩

@[simp] theorem boundary_primary (k : Fin 3) : boundary (primaryPort k)=copyVertex k 0 := by fin_cases k <;> rfl
@[simp] theorem boundary_black (k : Fin 3) : boundary (blackPort k)=copyVertex k 2 := by fin_cases k <;> rfl
@[simp] theorem boundary_gray (k : Fin 3) : boundary (grayPort k)=copyVertex (next k) 6 := by fin_cases k <;> rfl

def portColor (b : Fin 3 → Bool) : Fin 9 → Fin 3 :=
  ![boolColor (b 0),0,1,boolColor (b 1),0,1,boolColor (b 2),0,1]

@[simp] theorem extension_boundary (b : Fin 3 → Bool) (k : Fin 9) :
    extension b (boundary k)=portColor b k := by
  fin_cases k <;> dsimp [boundary,portColor] <;> rw [extension_copy] <;> rfl

@[simp] theorem portColor_primary (b : Fin 3 → Bool) (k : Fin 3) :
    portColor b (primaryPort k)=boolColor (b k) := by fin_cases k <;> rfl

/-- A boundary palette pair pins the internal reference too, through literal
palette-copying edges. No internal vertex is assumed externally accessible. -/
theorem boundary_pinned_iff (col : Vertex → Fin 3) :
    Proper col ∧ col (boundary 1)=0 ∧ col (boundary 2)=1 ↔
      ExactlyOne (inputBits col 0) (inputBits col 1) (inputBits col 2) ∧ col=extension (inputBits col) := by
  constructor
  · rintro ⟨hp,hb,hg⟩
    have hs := (proper_split col).mp hp
    have hc := PlanarColoringOneWayConverter.palette_copy (col ∘ copyVertex 0) (hs.1 0)
    have hw := (PlanarColoringExclusiveCrossing.proper_iff _).mp (hs.2.1 0)
    have hb' : col (copyVertex 0 7)=0 := hc.1.symm.trans hb
    have hgg : col (copyVertex 1 6)=col (copyVertex 0 4) := congrFun hw.2 3
    have hg' : col (copyVertex 0 6)=1 := (hgg.trans hc.2.1).symm.trans hg
    exact reconstruct col hp hb' hg'
  · rintro ⟨hb,he⟩
    rw [he]
    exact ⟨extension_proper _ hb,extension_boundary _ 1,extension_boundary _ 2⟩

@[simp] theorem labels_port (k : Fin 9) : labels (.inl k)=boundary k := rfl
@[simp] theorem labels_symm_boundary (k : Fin 9) : labels.symm (boundary k)=.inl k := by
  exact labels.symm_apply_apply (.inl k)

def PatchProper (col : Fin 9 ⊕ InternalVertex → Fin 3) : Prop :=
  ∀ e,col (patchGraph.src e)≠col (patchGraph.dst e)

def patchExtension (b : Fin 3 → Bool) : Fin 9 ⊕ InternalVertex → Fin 3 := extension b ∘ labels

@[simp] theorem patchExtension_port (b : Fin 3 → Bool) (k : Fin 9) :
    patchExtension b (.inl k)=portColor b k := extension_boundary b k

theorem patchProper_iff (col : Fin 9 ⊕ InternalVertex → Fin 3) :
    PatchProper col ↔ Proper (col ∘ labels.symm) := Iff.rfl

private theorem inputBits_of_ports (col : Fin 9 ⊕ InternalVertex → Fin 3) (b : Fin 3 → Bool)
    (h : ∀ k,col (.inl k)=portColor b k) : inputBits (col ∘ labels.symm)=b := by
  funext k
  change decide (col (labels.symm (copyVertex k 0))=2)=b k
  rw [← boundary_primary k,labels_symm_boundary,h,portColor_primary]
  cases b k <;> rfl

/-- Complete usable patch interface: exactly the satisfying Boolean triples
extend, and the entire coloring is the one explicit reconstructed extension. -/
theorem patch_spec_iff (col : Fin 9 ⊕ InternalVertex → Fin 3) (b : Fin 3 → Bool) :
    (PatchProper col ∧ ∀ k,col (.inl k)=portColor b k) ↔
      ExactlyOne (b 0) (b 1) (b 2) ∧ col=patchExtension b := by
  constructor
  · rintro ⟨hp,hports⟩
    have hbits := inputBits_of_ports col b hports
    have hc : Proper (col ∘ labels.symm) := (patchProper_iff col).mp hp
    have hb : (col ∘ labels.symm) (boundary 1)=0 := by
      simp only [Function.comp_apply,labels_symm_boundary,hports]
      rfl
    have hg : (col ∘ labels.symm) (boundary 2)=1 := by
      simp only [Function.comp_apply,labels_symm_boundary,hports]
      rfl
    have h := (boundary_pinned_iff (col ∘ labels.symm)).mp ⟨hc,hb,hg⟩
    rw [hbits] at h
    refine ⟨h.1,?_⟩
    funext v
    have he := congrFun h.2 (labels v)
    simpa only [Function.comp_apply,Equiv.symm_apply_apply,patchExtension] using he
  · rintro ⟨hb,rfl⟩
    refine ⟨?_,patchExtension_port b⟩
    rw [patchProper_iff]
    have he : patchExtension b ∘ labels.symm=extension b := by
      funext v
      simp [patchExtension]
    rw [he]
    exact extension_proper b hb

/-- Exact one-to-one local multiplicity in the form consumed by global gluing. -/
theorem patch_unique_extension (b : Fin 3 → Bool) :
    (∃! col : Fin 9 ⊕ InternalVertex → Fin 3,PatchProper col ∧ ∀ k,col (.inl k)=portColor b k) ↔
      ExactlyOne (b 0) (b 1) (b 2) := by
  constructor
  · rintro ⟨col,hc,_⟩
    exact ((patch_spec_iff col b).mp hc).1
  · intro hb
    refine ⟨patchExtension b,(patch_spec_iff _ b).mpr ⟨hb,rfl⟩,?_⟩
    intro col hc
    exact ((patch_spec_iff col b).mp hc).2

end PlanarHom.PlanarColoringClause
