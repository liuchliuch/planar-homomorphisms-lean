import PlanarHom.MixedRootedInstances

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MixedInstance
variable {V E F W J L C K:Type} {b u:ℕ}

structure Equivalence (G:MixedInstance V E F b u) (H:MixedInstance W J L b u) where
  vertex : V≃W
  edge : E≃J
  unary : F≃L
  src_eq : ∀e,H.graph.src (edge e)=vertex (G.graph.src e)
  dst_eq : ∀e,H.graph.dst (edge e)=vertex (G.graph.dst e)
  edgeLabel_eq : ∀e,H.edgeLabel (edge e)=G.edgeLabel e
  unaryHost_eq : ∀f,H.unaryHost (unary f)=vertex (G.unaryHost f)
  unaryLabel_eq : ∀f,H.unaryLabel (unary f)=G.unaryLabel f

variable [Fintype V] [Fintype E] [Fintype F] [Fintype W] [Fintype J] [Fintype L]
variable [Fintype C] [Field K]

theorem Equivalence.assignment {G:MixedInstance V E F b u} {H:MixedInstance W J L b u}
    (e:Equivalence G H) (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) (σ:W→C) :
    H.assignment M U w σ=G.assignment M U w (σ∘e.vertex) := by
  unfold MixedInstance.assignment
  rw [←e.vertex.prod_comp,←e.edge.prod_comp,←e.unary.prod_comp]
  simp only [e.src_eq,e.dst_eq,e.edgeLabel_eq,e.unaryHost_eq,e.unaryLabel_eq,Function.comp_apply]

theorem Equivalence.partition {G:MixedInstance V E F b u} {H:MixedInstance W J L b u}
    (e:Equivalence G H) (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) :
    H.partition M U w=G.partition M U w := by
  unfold MixedInstance.partition
  simp only [e.assignment]
  exact Fintype.sum_equiv (Equiv.arrowCongr e.vertex.symm (Equiv.refl C)) _ _ (fun _=>rfl)

end PlanarHom.MixedInstance
