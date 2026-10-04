import PlanarHom.PlanarRootedTreeExtraction

/-! NEW finite recursive occurrence trees. This is only combinatorial data:
compatibility checks every child occurrence against the literal parent/child
roots; vertex-list nodup imposes the ordinary tree condition. -/
namespace PlanarHom.MultiGraph
variable {V E : Type*}

inductive RootedOccurrenceTree (V E : Type*) where
  | node (root : V) (children : List (E × RootedOccurrenceTree V E)) : RootedOccurrenceTree V E

namespace RootedOccurrenceTree
variable {G : MultiGraph V E}

def root : RootedOccurrenceTree V E → V
  | .node v _ => v

def vertices : RootedOccurrenceTree V E → List V
  | .node v children => v :: children.flatMap (fun c => vertices c.2)
termination_by t => sizeOf t
decreasing_by
  rename_i children hc
  have h := List.sizeOf_lt_sizeOf_of_mem hc
  rcases c with ⟨e,t⟩
  simp only [Prod.mk.sizeOf_spec,RootedOccurrenceTree.node.sizeOf_spec] at *
  omega

def edges : RootedOccurrenceTree V E → List E
  | .node _ children => children.flatMap (fun c => c.1 :: edges c.2)
termination_by t => sizeOf t
decreasing_by
  rename_i children hc
  have h := List.sizeOf_lt_sizeOf_of_mem hc
  rcases c with ⟨e,t⟩
  simp only [Prod.mk.sizeOf_spec,RootedOccurrenceTree.node.sizeOf_spec] at *
  omega

def Compatible (G : MultiGraph V E) : RootedOccurrenceTree V E → Prop
  | .node v children => ∀ c∈children, G.src c.1=v ∧ G.dst c.1=c.2.root ∧ Compatible G c.2
termination_by t => sizeOf t
decreasing_by
  rename_i children hc
  have h := List.sizeOf_lt_sizeOf_of_mem hc
  rcases c with ⟨e,t⟩
  simp only [Prod.mk.sizeOf_spec,RootedOccurrenceTree.node.sizeOf_spec] at *
  omega

def Valid (G : MultiGraph V E) (tree : RootedOccurrenceTree V E) : Prop :=
  tree.Compatible G ∧ tree.vertices.Nodup

@[simp] theorem root_node (v : V) (children : List (E × RootedOccurrenceTree V E)) :
    (node v children).root=v := by rw [root]

@[simp] theorem vertices_node (v : V) (children : List (E × RootedOccurrenceTree V E)) :
    (node v children).vertices=v::children.flatMap (fun c => vertices c.2) := by rw [vertices]

@[simp] theorem edges_node (v : V) (children : List (E × RootedOccurrenceTree V E)) :
    (node v children).edges=children.flatMap (fun c => c.1::edges c.2) := by rw [edges]

@[simp] theorem compatible_node (v : V) (children : List (E × RootedOccurrenceTree V E)) :
    (node v children).Compatible G ↔
      ∀ c∈children, G.src c.1=v ∧ G.dst c.1=c.2.root ∧ c.2.Compatible G := by rw [Compatible]

theorem root_mem_vertices (tree : RootedOccurrenceTree V E) : tree.root∈tree.vertices := by
  cases tree
  simp

theorem child_valid {v : V} {children : List (E × RootedOccurrenceTree V E)}
    (ht : (node v children).Valid G) (c : E × RootedOccurrenceTree V E) (hc : c∈children) : c.2.Valid G := by
  have hv := ht.2
  rw [vertices_node] at hv
  have hf := (List.nodup_cons.mp hv).2
  exact ⟨((compatible_node _ _).mp ht.1 c hc).2.2,(List.nodup_flatMap.mp hf).1 c hc⟩

theorem root_notMem_child {v : V} {children : List (E × RootedOccurrenceTree V E)}
    (ht : (node v children).Valid G) (c : E × RootedOccurrenceTree V E) (hc : c∈children) : v∉c.2.vertices := by
  intro hv
  have hvv := ht.2
  rw [vertices_node] at hvv
  exact (List.nodup_cons.mp hvv).1 (List.mem_flatMap.mpr ⟨c,hc,hv⟩)

theorem child_nonloop {v : V} {children : List (E × RootedOccurrenceTree V E)}
    (ht : (node v children).Valid G) (c : E × RootedOccurrenceTree V E) (hc : c∈children) : G.src c.1≠G.dst c.1 := by
  rw [((compatible_node _ _).mp ht.1 c hc).1,((compatible_node _ _).mp ht.1 c hc).2.1]
  intro he
  exact root_notMem_child ht c hc (he.symm ▸ c.2.root_mem_vertices)

end RootedOccurrenceTree
end PlanarHom.MultiGraph
