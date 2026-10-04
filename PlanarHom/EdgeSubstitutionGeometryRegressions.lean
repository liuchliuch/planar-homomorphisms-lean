import PlanarHom.TypedGadgetAppendMachines
import PlanarHom.TypedGadgetAppendReduction

/-! Boundary regression checks for the literal allocation bijection and its
unchanged typed promise/reduction/machine consumers. -/
noncomputable section
namespace PlanarHom.EdgeSubstitution.GeometryRegressions
open Complexity FixedGadgetNetwork

example (ts : List Template) : substitute ts (⟨0,[],[]⟩ : MixedCode)=⟨0,[],[]⟩ := rfl
example : substitute [] (⟨3,[],[(2,0)]⟩ : MixedCode)=⟨3,[],[(2,0)]⟩ := rfl

/-- Two equal loop occurrences receive distinct private vertices, and the
unrelated old isolate remains present with its unary occurrence. -/
example : substitute [⟨2,1,[(0,2,0),(2,1,0)],[]⟩]
    (⟨2,[(0,0,0),(0,0,0)],[(1,0)]⟩ : MixedCode) =
    ⟨4,[(0,2,0),(2,0,0),(0,3,0),(3,0,0)],[(1,0)]⟩ := by decide

/-- An empty gadget deletes no old vertices and allocates no fictional edges. -/
example : substitute [⟨2,0,[],[]⟩]
    (⟨3,[(0,1,0),(0,0,0)],[(2,0)]⟩ : MixedCode) = ⟨3,[],[(2,0)]⟩ := by decide

/-- Private isolates are allocated for each occurrence even with no local edge. -/
example : substitute [⟨2,2,[],[]⟩]
    (⟨1,[(0,0,0),(0,0,0)],[]⟩ : MixedCode) = ⟨5,[],[]⟩ := by decide

example (ts : List Template) (g : MixedCode) (v : Fin g.vertices) :
    (substitutionVertices ts g (.inl v)).val = v.val := substitutionVertices_old ts g v

example (ts : List Template) {bt ut : ℕ}
    (ht : ∀ t∈ts,t.code.Valid bt ut) (hb : ∀ t∈ts,t.boundary=2)
    (g : MixedCode) (hg : g.Valid ts.length ut) :
    MultiGraph.IncidenceEquiv
      ((g.toMultiGraph hg).insertFamily (selectedGadget ts ht hb g hg))
      ((substitute ts g).toMultiGraph (substitute_valid ts ht hb g hg)) :=
  substitutionIncidence ts ht hb g hg

example (ts : List Template) {bt ut : ℕ}
    (ht : ∀t∈ts,t.code.Valid bt ut) (hb : ∀t∈ts,t.boundary=2)
    (hp : ∀t (h:t∈ts),TwoTerminal.PlanarEdgeGadget (t.edgeGadget (hb t h) (ht t h)))
    (g : MixedCode) (hg : g.PlanarValid ts.length ut) :
    (substitute ts g).PlanarValid bt ut := substitute_planarValid ts ht hb hp g hg

end PlanarHom.EdgeSubstitution.GeometryRegressions
