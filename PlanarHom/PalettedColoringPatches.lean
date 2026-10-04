import PlanarHom.ColoringPatchComposition
import PlanarHom.ColoringClausePaletteState

/-! Exact local interfaces for the actual macro graph family. A verified
coloring equivalence and its literal port values imply unique gluing; no local
truth table, uniqueness statement, or palette normalization is assumed silently.
-/
noncomputable section
open Classical
namespace PlanarHom.PalettedColoringPatches
open MultiGraph ThreeColorPaletteCounting PlanarColoringClause


def triple (p : Palette) (b : Bool) : Fin 3 → Fin 3 :=
  ![palettePermutation p (boolColor b),p.val.2,p.val.1]
@[simp] theorem triple_primary (p : Palette) (b : Bool) : triple p b 0=palettePermutation p (boolColor b) := rfl
@[simp] theorem triple_gray (p : Palette) (b : Bool) : triple p b 1=p.val.2 := rfl
@[simp] theorem triple_black (p : Palette) (b : Bool) : triple p b 2=p.val.1 := rfl

abbrev State (P : Type) (accepted : (P → Bool) → Prop) := Palette × {b : P → Bool // accepted b}

def portColor {P : Type} {accepted : (P → Bool) → Prop} (s : State P accepted) : P × Fin 3 → Fin 3 :=
  fun p => triple s.1 (s.2.val p.1) p.2

theorem portColor_injective {P : Type} [Nonempty P] (accepted : (P → Bool) → Prop) :
    Function.Injective (@portColor P accepted) := by
  rintro ⟨p,b⟩ ⟨q,c⟩ h
  let k : P := Classical.choice ‹Nonempty P›
  have hb := congrFun h (k,2)
  have hg := congrFun h (k,1)
  have hp : p=q := Subtype.ext (Prod.ext hb hg)
  subst q
  have hc : b=c := by
    apply Subtype.ext
    funext k
    have hh := congrFun h (k,0)
    exact boolColor_injective ((palettePermutation p).injective hh)
  subst c
  rfl

structure Patch (P W E : Type) where
  graph : MultiGraph ((P × Fin 3) ⊕ W) E
  accepted : (P → Bool) → Prop
  equiv : Coloring graph ≃ State P accepted
  ports : ∀ col p,col.val (.inl p)=portColor (equiv col) p

namespace Patch
variable {P W E : Type} [Nonempty P] (L : Patch P W E)

def BoundaryRelation (b : P × Fin 3 → Fin 3) : Prop := ∃ s : State P L.accepted,b=portColor s

def InsideExtension (b : P × Fin 3 → Fin 3) : W → Fin 3 :=
  if h : L.BoundaryRelation b then (L.equiv.symm h.choose).val ∘ Sum.inr else fun _ => 0

@[simp] theorem inverse_port (s : State P L.accepted) (p : P × Fin 3) :
    (L.equiv.symm s).val (.inl p)=portColor s p := by
  rw [L.ports,L.equiv.apply_symm_apply]

theorem proper_iff_state (b : P × Fin 3 → Fin 3) (u : W → Fin 3) :
    (∀ e,Sum.elim b u (L.graph.src e)≠Sum.elim b u (L.graph.dst e)) ↔
      ∃ s : State P L.accepted,b=portColor s ∧ u=(L.equiv.symm s).val ∘ Sum.inr := by
  constructor
  · intro hp
    let col : Coloring L.graph := ⟨Sum.elim b u,hp⟩
    refine ⟨L.equiv col,?_,?_⟩
    · funext p
      exact L.ports col p
    · have he := congrArg Subtype.val (L.equiv.symm_apply_apply col)
      funext w
      exact (congrFun he (.inr w)).symm
  · rintro ⟨s,hb,hu⟩
    have he : Sum.elim b u=(L.equiv.symm s).val := by
      funext v
      cases v with
      | inl p => exact (congrFun hb p).trans (L.inverse_port s p).symm
      | inr w => exact congrFun hu w
    rw [he]
    exact (L.equiv.symm s).property

/-- The precise uniqueness interface needed by the literal port-patch gluing
constructor, including boundary assignments that admit no coloring. -/
theorem local_unique (b : P × Fin 3 → Fin 3) (u : W → Fin 3) :
    (∀ e,Sum.elim b u (L.graph.src e)≠Sum.elim b u (L.graph.dst e)) ↔
      L.BoundaryRelation b ∧ u=L.InsideExtension b := by
  rw [L.proper_iff_state]
  constructor
  · rintro ⟨s,hb,hu⟩
    have h : L.BoundaryRelation b := ⟨s,hb⟩
    refine ⟨h,?_⟩
    have hs : s=h.choose := portColor_injective L.accepted (hb.symm.trans h.choose_spec)
    rw [InsideExtension,dif_pos h,←hs]
    exact hu
  · rintro ⟨h,hu⟩
    refine ⟨h.choose,h.choose_spec,?_⟩
    simpa only [InsideExtension,dif_pos h] using hu

end Patch

variable {C S : Type} {P W E : C → Type} [∀ c,Nonempty (P c)]
variable (L : ∀ c,Patch (P c) (W c) (E c)) (signal : ∀ c,P c → S)

def placePort (c : C) (p : P c × Fin 3) : S × Fin 3 := (signal c p.1,p.2)
def graph : MultiGraph ((S × Fin 3) ⊕ Sigma W) (Sigma E) :=
  PortPatchAssembly.graph (fun c => (L c).graph) (placePort signal)

def Relation (c : C) (b : S × Fin 3 → Fin 3) : Prop :=
  (L c).BoundaryRelation (b ∘ placePort signal c)

def extension (c : C) (b : S × Fin 3 → Fin 3) : W c → Fin 3 :=
  (L c).InsideExtension (b ∘ placePort signal c)

def coloringEquiv : Coloring (graph L signal) ≃
    {b : S × Fin 3 → Fin 3 // ∀ c,Relation L signal c b} :=
  ColoringPatchComposition.coloringEquiv (fun c => (L c).graph) (placePort signal)
    (Relation L signal) (extension L signal) (fun c b u => (L c).local_unique _ u)

end PlanarHom.PalettedColoringPatches
