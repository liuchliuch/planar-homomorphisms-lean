import PlanarHom.RootedConditionalSemantics
import PlanarHom.MixedParallelSemantics

/-! Typed mixed instances and rooted signatures with every occurrence retained.
Binary and unary labels are actual finite-language data, not a homogeneous
replacement. A rooted signature omits exactly the root's background factor. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom

structure MixedInstance (V E F:Type) (b u:ℕ) where
  graph : MultiGraph V E
  edgeLabel : E→Fin b
  unaryHost : F→V
  unaryLabel : F→Fin u

namespace MixedInstance
variable {V E F W J L C K:Type} {b u:ℕ}
variable [Fintype V] [Fintype E] [Fintype F] [Fintype C] [Field K]

def assignment (G:MixedInstance V E F b u) (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K)
    (σ:V→C) : K :=
  (∏v,w (σ v))*(∏e,M (G.edgeLabel e) (σ (G.graph.src e)) (σ (G.graph.dst e)))*
    ∏f,U (G.unaryLabel f) (σ (G.unaryHost f))

def partition (G:MixedInstance V E F b u) (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) : K :=
  ∑σ:V→C,G.assignment M U w σ

def rootRestricted (G:MixedInstance V E F b u) (r:V) (M:Fin b→Matrix C C K)
    (U:Fin u→C→K) (w:C→K) (X:Set C) : K :=
  ∑σ:V→C,if σ r∈X then G.assignment M U w σ else 0

/-- Vertex reindexing preserves each binary and unary occurrence and label. -/
def reindexVertex (G:MixedInstance V E F b u) (e:V≃W) : MixedInstance W E F b u where
  graph:=G.graph.reindex e (Equiv.refl E)
  edgeLabel:=G.edgeLabel
  unaryHost:=e∘G.unaryHost
  unaryLabel:=G.unaryLabel

variable [Fintype W]

theorem assignment_reindexVertex (G:MixedInstance V E F b u) (e:V≃W) (M:Fin b→Matrix C C K)
    (U:Fin u→C→K) (w:C→K) (σ:W→C) :
    (G.reindexVertex e).assignment M U w σ=G.assignment M U w (σ∘e) := by
  unfold assignment
  congr 2
  · exact (e.prod_comp (fun v=>w (σ v))).symm

theorem partition_reindexVertex (G:MixedInstance V E F b u) (e:V≃W) (M:Fin b→Matrix C C K)
    (U:Fin u→C→K) (w:C→K) : (G.reindexVertex e).partition M U w=G.partition M U w := by
  unfold partition
  simp only [assignment_reindexVertex]
  exact Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl C)) _ _ (fun _=>rfl)

theorem rootRestricted_reindexVertex (G:MixedInstance V E F b u) (e:V≃W) (r:V)
    (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) (X:Set C) :
    (G.reindexVertex e).rootRestricted (e r) M U w X=G.rootRestricted r M U w X := by
  unfold rootRestricted
  simp only [assignment_reindexVertex]
  exact Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl C)) _ _ (fun _=>rfl)

end MixedInstance

abbrev MixedRooted (V E F:Type) (b u:ℕ) := MixedInstance (PUnit.{1}⊕V) E F b u
namespace MixedRooted
variable {V E F C K:Type} {b u:ℕ}
variable [Fintype V] [Fintype E] [Fintype F] [Fintype C] [Field K]

def signature (G:MixedRooted V E F b u) (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) : C→K :=
  fun i=>∑σ:V→C,(∏v,w (σ v))*
    (∏e,M (G.edgeLabel e) (RootedGraph.extend i σ (G.graph.src e)) (RootedGraph.extend i σ (G.graph.dst e)))*
    ∏f,U (G.unaryLabel f) (RootedGraph.extend i σ (G.unaryHost f))

theorem assignment_extend (G:MixedRooted V E F b u) (M:Fin b→Matrix C C K) (U:Fin u→C→K)
    (w:C→K) (i:C) (σ:V→C) : G.assignment M U w (RootedGraph.extend i σ)=
      w i*((∏v,w (σ v))*(∏e,M (G.edgeLabel e) (RootedGraph.extend i σ (G.graph.src e))
        (RootedGraph.extend i σ (G.graph.dst e)))*∏f,U (G.unaryLabel f) (RootedGraph.extend i σ (G.unaryHost f))) := by
  simp [MixedInstance.assignment,RootedGraph.extend,Fintype.prod_sum_type,mul_assoc]

theorem rootRestricted_signature (G:MixedRooted V E F b u) (M:Fin b→Matrix C C K)
    (U:Fin u→C→K) (w:C→K) (X:Set C) :
    G.rootRestricted (.inl PUnit.unit) M U w X=
      RootedSignatureSpan.pairing w (fun i=>if i∈X then 1 else 0) (signature G M U w) := by
  unfold MixedInstance.rootRestricted
  rw [RootedGraph.sum_root_assignments]
  simp only [assignment_extend]
  unfold RootedSignatureSpan.pairing
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hx:i∈X
  · simp only [RootedGraph.extend,Sum.elim_inl,hx,ite_true,assignment_extend,mul_one,signature,Finset.mul_sum]
  · simp [RootedGraph.extend,hx]

end MixedRooted
end PlanarHom
