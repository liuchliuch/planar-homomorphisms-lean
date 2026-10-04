import PlanarHom.MixedRootedInstances
import PlanarHom.RootedPlanarity

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MixedInstance
variable {V E F W J L C K:Type} {b u:ℕ}

def attach (G:MixedInstance V E F b u) (H:MixedRooted W J L b u) (r:V) :
    MixedInstance (V⊕W) (E⊕J) (F⊕L) b u where
  graph:=G.graph.attachRooted H.graph r
  edgeLabel:=Sum.elim G.edgeLabel H.edgeLabel
  unaryHost:=Sum.elim (Sum.inl∘G.unaryHost) (MultiGraph.attachRootedVertex r∘H.unaryHost)
  unaryLabel:=Sum.elim G.unaryLabel H.unaryLabel

variable [Fintype V] [Fintype E] [Fintype F] [Fintype W] [Fintype J] [Fintype L]
variable [Fintype C] [Field K]

@[simp] theorem sum_attach_vertex (r:V) (σ:V→C) (τ:W→C) (a:PUnit⊕W) :
    Sum.elim σ τ (MultiGraph.attachRootedVertex r a)=RootedGraph.extend (σ r) τ a := by
  cases a <;> rfl

theorem assignment_attach (G:MixedInstance V E F b u) (H:MixedRooted W J L b u) (r:V)
    (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) (σ:V→C) (τ:W→C) :
    (G.attach H r).assignment M U w (Sum.elim σ τ)=G.assignment M U w σ *
      ((∏v,w (τ v))*(∏e,M (H.edgeLabel e) (RootedGraph.extend (σ r) τ (H.graph.src e))
        (RootedGraph.extend (σ r) τ (H.graph.dst e)))*
        ∏f,U (H.unaryLabel f) (RootedGraph.extend (σ r) τ (H.unaryHost f))) := by
  simp only [assignment,attach,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,
    MultiGraph.attachRooted,Function.comp_apply,sum_attach_vertex]
  ring

theorem partition_attach (G:MixedInstance V E F b u) (H:MixedRooted W J L b u) (r:V)
    (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) :
    (G.attach H r).partition M U w=
      ∑σ:V→C,G.assignment M U w σ*MixedRooted.signature H M U w (σ r) := by
  unfold partition
  rw [TwoTerminal.sum_colorings_sum]
  simp only [assignment_attach,MixedRooted.signature,Finset.mul_sum]

end PlanarHom.MixedInstance
namespace PlanarHom.MixedRooted
variable {V E F W J L C K:Type} {b u:ℕ}
variable [Fintype V] [Fintype E] [Fintype F] [Fintype W] [Fintype J] [Fintype L]
variable [Fintype C] [Field K]

theorem partition_attach_root (G:MixedRooted V E F b u) (H:MixedRooted W J L b u)
    (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) :
    (G.attach H (.inl PUnit.unit)).partition M U w=
      RootedSignatureSpan.pairing w (signature G M U w) (signature H M U w) := by
  rw [MixedInstance.partition_attach,RootedGraph.sum_root_assignments]
  simp only [assignment_extend]
  simp only [assignment_extend,RootedGraph.extend,Sum.elim_inl,RootedSignatureSpan.pairing,signature,
    Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

/-- Reindex only private vertices; all occurrence indices and labels remain. -/
def reindex (G:MixedRooted V E F b u) (e:V≃W) : MixedRooted W E F b u :=
  G.reindexVertex (Equiv.sumCongr (Equiv.refl PUnit.{1}) e)

theorem signature_reindex (G:MixedRooted V E F b u) (e:V≃W)
    (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) :
    signature (G.reindex e) M U w=signature G M U w := by
  funext i
  unfold signature
  apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl C))
  intro σ
  simp only [Equiv.arrowCongr,Equiv.coe_fn_mk,Equiv.refl_apply,Function.comp_apply,
    Equiv.symm_symm,Function.comp_def]
  have hx:∀v:PUnit.{1}⊕V,RootedGraph.extend i σ ((Equiv.sumCongr (Equiv.refl PUnit.{1}) e) v)=
      RootedGraph.extend i (fun v=>σ (e v)) v:=by intro v; cases v <;> rfl
  simp only [reindex,MixedInstance.reindexVertex,MultiGraph.reindex,Equiv.refl_symm,Equiv.refl_apply,hx,
    Function.comp_apply]
  congr 2
  exact (e.prod_comp (fun v=>w (σ v))).symm

end PlanarHom.MixedRooted
