import PlanarHom.PlanarityLRFaceComponents
import PlanarHom.PlanarityLRContourCycles
import PlanarHom.PlanarityLRRootedTreeComponents

/-! NEW actual DFS-component incidence graph, retaining original occurrence directions. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints

abbrev ComponentVertex (g : MixedCode) (r : ℕ) := {v:Fin g.vertices // componentRoot g v.val=r}
abbrev ComponentEdge (g : MixedCode) (r : ℕ) := {e:Fin g.edges.length // componentRoot g (source g e.val)=r}

theorem dartHost_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (a : Dart (Fin g.edges.length)) :
    componentRoot g (dartHost g a)=componentRoot g (source g a.1.val) := by
  obtain ⟨e,rfl | rfl⟩:=exists_typedOutward g a
  · rw [dartHost_typedOutward]
    rfl
  · rw [dartHost_reverse_typedOutward]
    exact (source_target_componentRoot g hg e.isLt).symm

theorem original_host_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (a : Dart (Fin g.edges.length)) :
    componentRoot g ((g.toMultiGraph hg).dartPair a).1.val=componentRoot g (source g a.1.val) := by
  rw [←eraseDart_host g hg a]
  exact dartHost_componentRoot g hg a

def componentGraph (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ) :
    MultiGraph (ComponentVertex g r) (ComponentEdge g r) where
  src e := ⟨(g.toMultiGraph hg).src e.val,(original_host_componentRoot g hg (e.val,true)).trans e.property⟩
  dst e := ⟨(g.toMultiGraph hg).dst e.val,(original_host_componentRoot g hg (e.val,false)).trans e.property⟩

def componentDartLift (g : MixedCode) (r : ℕ) (a : Dart (ComponentEdge g r)) : Dart (Fin g.edges.length) :=
  (a.1.val,a.2)

theorem componentDartLift_injective (g : MixedCode) (r : ℕ) : Function.Injective (componentDartLift g r) := by
  intro a b h
  exact Prod.ext (Subtype.ext (congrArg (fun x:Dart (Fin g.edges.length)=>x.1) h))
    (congrArg (fun x:Dart (Fin g.edges.length)=>x.2) h)

theorem componentDartLift_host (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (a : Dart (ComponentEdge g r)) :
    ((componentGraph g hg r).dartPair a).1.val=((g.toMultiGraph hg).dartPair (componentDartLift g r a)).1 := by
  rcases a with ⟨e,b⟩
  cases b <;> rfl

@[simp] theorem componentDartLift_reverse (g : MixedCode) (r : ℕ) (a : Dart (ComponentEdge g r)) :
    componentDartLift g r (reversePerm _ a)=reversePerm _ (componentDartLift g r a) := rfl

def componentDartEquiv (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ) :
    Dart (ComponentEdge g r) ≃ {a:Dart (Fin g.edges.length) // componentRoot g (dartHost g a)=r} where
  toFun a := ⟨componentDartLift g r a,(dartHost_componentRoot g hg _).trans a.1.property⟩
  invFun a := (⟨a.val.1,(dartHost_componentRoot g hg a.val).symm.trans a.property⟩,a.val.2)
  left_inv a := rfl
  right_inv a := rfl

end PlanarHom.PlanarityLRRealization
