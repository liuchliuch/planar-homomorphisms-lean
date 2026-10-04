import PlanarHom.SurfaceRotationHomology
import PlanarHom.PottsComponentRank

/-! NEW supplied orientable-surface representation. Its ribbon data are the
literal graph and cyclic rows. Complement regions carry only their genera and
boundary attachments. Connectivity is checked on the actual bipartite incidence
graph. No homology, Pfaffian-sign, or genus-bound certificate is an input. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceRibbonComplement
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

abbrev Component := G.Components Finset.univ
abbrev Isolated := {v:V // ∀a:Dart E,(G.dartPair a).1≠v}

/-- A fixed enumeration interface prevents vertex-decision implementations from
changing the boundary-count expression when specializing generic gluing data. -/
instance (priority := 10000) isolatedFintype : Fintype (Isolated (G:=G)) := Fintype.ofFinite _
/-- Actual ribbon boundary circles: ordinary dart-face cycles, plus the single
circle around each isolated vertex. -/
abbrev Boundary := R.Face ⊕ Isolated (G:=G)

def vertexComponent (v : V) : Component (G:=G) := Quotient.mk _ v

theorem reverse_component (a : Dart E) :
    vertexComponent (G:=G) (G.dartPair (reversePerm E a)).1=
      vertexComponent (G:=G) (G.dartPair a).1 := by
  rcases a with ⟨e,b⟩
  have h:vertexComponent (G:=G) (G.src e)=vertexComponent (G:=G) (G.dst e) :=
    Quotient.sound (Relation.EqvGen.rel _ _ ⟨e,Finset.mem_univ _,rfl,rfl⟩)
  cases b
  · simpa [reversePerm,dartPair] using h
  · simpa [reversePerm,dartPair] using h.symm

 theorem face_step_component (a : Dart E) :
    vertexComponent (G:=G) (G.dartPair (R.facePerm a)).1=
      vertexComponent (G:=G) (G.dartPair a).1 := by
  rw [R.facePerm_host]
  exact reverse_component a

 theorem face_cycle_component (a b : Dart E) (h:R.facePerm.SameCycle a b) :
    vertexComponent (G:=G) (G.dartPair a).1=vertexComponent (G:=G) (G.dartPair b).1 := by
  obtain ⟨n,hn⟩:=h.exists_nat_pow_eq
  have hi:∀n,vertexComponent (G:=G) (G.dartPair (R.facePerm^[n] a)).1=
      vertexComponent (G:=G) (G.dartPair a).1 := by
    intro n
    induction n with
    | zero=>rfl
    | succ n ih=>rw [Function.iterate_succ_apply',face_step_component,ih]
  have hh:=hi n
  rw [Equiv.Perm.iterate_eq_pow,hn] at hh
  exact hh.symm

 def faceComponent : R.Face→Component (G:=G) :=
  Quotient.lift (fun a=>vertexComponent (G:=G) (G.dartPair a).1)
    (fun a b h=>face_cycle_component R a b h)

 def boundaryComponent : Boundary R→Component (G:=G)
  | .inl f=>faceComponent R f
  | .inr v=>vertexComponent v.val

/-- Supplied complement pieces. Region j is the connected orientable surface
of genus regionGenus j whose boundary circles are exactly attachment⁻¹(j).
A closed complementary region, including all unused handles, is allowed. -/
structure Data where
  regions : ℕ
  attachment : Boundary R→Fin regions
  regionGenus : Fin regions→ℕ

variable {R}

 def Data.incidence (D : Data R) : MultiGraph (Component (G:=G)⊕Fin D.regions) (Boundary R) where
  src b:=.inl (boundaryComponent R b)
  dst b:=.inr (D.attachment b)

/-- Finite validation of a connected closed ambient genus-g surface encoded by
ribbon neighborhoods glued to the supplied complement pieces. Euler additivity
uses each boundary circle once on each side and its Euler characteristic zero. -/
def Data.Valid (D : Data R) (g : ℕ) : Prop :=
  0<D.regions ∧
  (∀u v,D.incidence.componentSetoid Finset.univ u v) ∧
  2*g+Fintype.card V+2*D.regions=
    Fintype.card E+Fintype.card (Boundary R)+2+2*∑j,D.regionGenus j

end PlanarHom.SurfaceRibbonComplement
