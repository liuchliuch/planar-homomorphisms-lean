import PlanarHom.PalettedColoringPatches
import PlanarHom.PottsRandomCluster

/-! Connectivity is a consequence of the verified local coloring bijection,
not an extra gadget assumption. An isolated component can be recolored without
changing any ports, contradicting uniqueness. -/
noncomputable section
open Classical
namespace PlanarHom.PalettedColoringPatches
open MultiGraph ThreeColorPaletteCounting PlanarColoringClause

namespace Connectivity
variable {V E : Type} [Fintype E] (G : MultiGraph V E)
def component (v : V) : G.Components Finset.univ := Quotient.mk _ v

theorem edge (e : E) : component G (G.src e)=component G (G.dst e) :=
  Quotient.sound (Relation.EqvGen.rel _ _ ⟨e,Finset.mem_univ _,rfl,rfl⟩)

def recolor (c : Coloring G) (q : G.Components Finset.univ) (π : Equiv.Perm (Fin 3)) : Coloring G :=
  ⟨fun v => if component G v=q then π (c.val v) else c.val v,by
    intro e
    dsimp only
    have h := edge G e
    by_cases hq : component G (G.src e)=q
    · rw [if_pos hq,if_pos (h.symm.trans hq)]
      exact fun he => c.property e (π.injective he)
    · rw [if_neg hq,if_neg (fun he => hq (h.trans he))]
      exact c.property e⟩

theorem forced_ne_connected (existsColoring : Nonempty (Coloring G)) (u v : V)
    (hne : ∀c : Coloring G,c.val u≠c.val v) : component G u=component G v := by
  by_contra h
  let c := Classical.choice existsColoring
  let d := recolor G c (component G u) (Equiv.swap (c.val u) (c.val v))
  apply hne d
  simp [d,recolor,Ne.symm h]

end Connectivity

namespace Patch
variable {P W E : Type} [Nonempty P] [Fintype E] (L : Patch P W E)
variable (existsColoring : Nonempty (Coloring L.graph))

def rootPort (_L : Patch P W E) : P := Classical.choice ‹Nonempty P›
def rootVertex : (P × Fin 3) ⊕ W := .inl (L.rootPort,2)

theorem black_gray_ne (c : Coloring L.graph) (p q : P) :
    c.val (.inl (p,2))≠c.val (.inl (q,1)) := by
  rw [L.ports,L.ports]
  exact (L.equiv c).1.property

theorem primary_gray_ne (c : Coloring L.graph) (p q : P) :
    c.val (.inl (p,0))≠c.val (.inl (q,1)) := by
  rw [L.ports,L.ports]
  change palettePermutation (L.equiv c).1 (boolColor ((L.equiv c).2.val p))≠(L.equiv c).1.val.2
  have hh : palettePermutation (L.equiv c).1 1=(L.equiv c).1.val.2 := rfl
  rw [←hh]
  apply (palettePermutation (L.equiv c).1).injective.ne
  cases (L.equiv c).2.val p <;> decide

include existsColoring in
theorem port_connected (p : P × Fin 3) :
    Connectivity.component L.graph (.inl p)=Connectivity.component L.graph L.rootVertex := by
  obtain ⟨p,k⟩ := p
  have hg (q : P) : Connectivity.component L.graph (.inl (q,1))=
      Connectivity.component L.graph L.rootVertex :=
    Connectivity.forced_ne_connected L.graph existsColoring _ _
      (fun c => (L.black_gray_ne c L.rootPort q).symm)
  fin_cases k
  · exact (Connectivity.forced_ne_connected L.graph existsColoring _ _
      (fun c => L.primary_gray_ne c p L.rootPort)).trans (hg L.rootPort)
  · exact hg p
  · exact (Connectivity.forced_ne_connected L.graph existsColoring _ _
      (fun c => L.black_gray_ne c p L.rootPort)).trans (hg L.rootPort)

include existsColoring in
/-- Every vertex belongs to the component of the exposed black palette rail. -/
theorem connected_root (v : (P × Fin 3) ⊕ W) :
    Connectivity.component L.graph v=Connectivity.component L.graph L.rootVertex := by
  by_contra hv
  let c : Coloring L.graph := Classical.choice existsColoring
  let other : Fin 3 := if c.val v=0 then 1 else 0
  have ho : c.val v≠other := by
    dsimp [other]
    split_ifs with h
    · simpa [h]
    · exact h
  let d := Connectivity.recolor L.graph c (Connectivity.component L.graph v) (Equiv.swap (c.val v) other)
  have hports : ∀p,d.val (.inl p)=c.val (.inl p) := by
    intro p
    have hp : Connectivity.component L.graph (.inl p)≠Connectivity.component L.graph v :=
      fun he => hv (he.symm.trans (L.port_connected existsColoring p))
    simp [d,Connectivity.recolor,hp]
  have hs : L.equiv d=L.equiv c := by
    apply portColor_injective L.accepted
    funext p
    rw [←L.ports,←L.ports]
    exact hports p
  have hd : d=c := L.equiv.injective hs
  have hc := congrArg (fun col : Coloring L.graph => col.val v) hd
  have hdv : d.val v=other := by simp [d,Connectivity.recolor]
  exact ho (hdv.symm.trans hc).symm

include existsColoring in
theorem connected (u v : (P × Fin 3) ⊕ W) :
    L.graph.componentSetoid Finset.univ u v :=
  Quotient.exact ((L.connected_root existsColoring u).trans (L.connected_root existsColoring v).symm)

include existsColoring in
/-- The actual edge occurrence set has no isolated vertices. -/
theorem incident (v : (P × Fin 3) ⊕ W) :
    ∃e,L.graph.src e=v ∨ L.graph.dst e=v := by
  by_contra h
  have hn (e : E) : L.graph.src e≠v ∧ L.graph.dst e≠v := by
    constructor
    · intro he; exact h ⟨e,Or.inl he⟩
    · intro he; exact h ⟨e,Or.inr he⟩
  let other : (P × Fin 3) ⊕ W :=
    if v=L.rootVertex then .inl (L.rootPort,1) else L.rootVertex
  have ho : other≠v := by
    dsimp [other]
    split_ifs with hv
    · subst v
      simp [rootVertex]
    · exact Ne.symm hv
  let indicator : (P × Fin 3) ⊕ W → Bool := fun x => if x=v then true else false
  have hc : L.graph.EdgeConstant Finset.univ indicator := by
    intro e _
    simp [indicator,(hn e).1,(hn e).2]
  have he := L.graph.edgeConstant_respects Finset.univ indicator hc
    (L.connected existsColoring v other)
  simp [indicator,ho] at he

end Patch
end PlanarHom.PalettedColoringPatches
