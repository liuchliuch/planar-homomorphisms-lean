import PlanarHom.MixedRootedCodeSemantics
import PlanarHom.MixedTotalEvaluation

/-! The finite weighted projection argument for an arbitrary retained finite
mixed language. Root sets are arbitrary; no all-vertex restriction is inferred
without a separate common-support or orientation propagation theorem. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom

def FiniteMixedRooted (b u:ℕ) := Σ n m k:ℕ,
  {G:MixedRooted (Fin n) (Fin m) (Fin k) b u //G.graph.Planar}

namespace MixedInstance
variable {V E F W J L C K:Type} {b u:ℕ}
variable [Fintype V] [Fintype E] [Fintype F] [Fintype W] [Fintype J] [Fintype L]
variable [Fintype C] [Field K]

theorem partition_attach_reindex (G:MixedInstance V E F b u) (e:V≃W)
    (H:MixedRooted J L (Fin 0) b u) (r:V) (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) :
    ((G.reindexVertex e).attach H (e r)).partition M U w=(G.attach H r).partition M U w := by
  rw [partition_attach,partition_attach]
  apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl C))
  intro σ
  rw [assignment_reindexVertex]
  rfl

/-- The same reindexing law retains an arbitrary unary occurrence type. -/
theorem partition_attach_reindex_all {T:Type} [Fintype T]
    (G:MixedInstance V E F b u) (e:V≃W)
    (H:MixedRooted J L T b u) (r:V) (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) :
    ((G.reindexVertex e).attach H (e r)).partition M U w=(G.attach H r).partition M U w := by
  rw [partition_attach,partition_attach]
  apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl C))
  intro σ
  rw [assignment_reindexVertex]
  rfl

def finiteRootEquiv (r:V) : V≃PUnit.{1}⊕Fin (Fintype.card {v:V//v≠r}) :=
  (MultiGraph.rootEquiv r).trans (Equiv.sumCongr (Equiv.refl PUnit.{1}) (Fintype.equivFin _))

@[simp] theorem finiteRootEquiv_root (r:V) : finiteRootEquiv r r=.inl PUnit.unit := by
  simp [finiteRootEquiv]

def finiteRootPresentation {m k:ℕ} (G:MixedInstance V (Fin m) (Fin k) b u) (r:V)
    (hp:G.graph.Planar) : FiniteMixedRooted b u :=
  ⟨Fintype.card {v:V//v≠r},m,k,G.reindexVertex (finiteRootEquiv r),
    (MultiGraph.planar_reindex_iff G.graph _ _).mpr hp⟩

end MixedInstance
namespace MixedRootedRestriction
open Complexity Complexity.MixedCode
variable {b u:ℕ} {C K:Type} [Fintype C] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def signature (H:FiniteMixedRooted b u) (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) : C→K :=
  MixedRooted.signature H.2.2.2.val M U w

theorem exists_computed_queries (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K)
    (hw:∀i,0 < w i) (X:Set C) :
    ∃s:ℕ,∃graphs:Fin s→FiniteMixedRooted b u,∃c:Fin s→K,
      ∀g:MixedCode,∀hg:g.PlanarValid b u,∀r:Fin g.vertices,
        (g.toMixedInstance hg.1).rootRestricted r M U w X=
          ∑j,c j*totalEvaluation M U w (MixedRootedCodeMachines.attach (graphs j).2.2.2.val (r.val,g)) := by
  obtain ⟨s,graphs,c,h⟩:=RootedSignatureSpan.exists_family_coefficients w hw
    (fun H:FiniteMixedRooted b u=>signature H M U w) (fun i=>if i∈X then 1 else 0)
  refine ⟨s,graphs,c,?_⟩
  intro g hg r
  let G:=g.toMixedInstance hg.1
  have hp:G.graph.Planar:=(MixedCode.planarValid_iff g hg.1).mp hg
  let H:=G.finiteRootPresentation r hp
  have he:=h H
  have hroot:(H.2.2.2.val).rootRestricted (.inl PUnit.unit) M U w X=G.rootRestricted r M U w X := by
    have hh:=G.rootRestricted_reindexVertex (MixedInstance.finiteRootEquiv r) r M U w X
    simpa only [MixedInstance.finiteRootEquiv_root] using hh
  rw [←hroot,MixedRooted.rootRestricted_signature]
  change RootedSignatureSpan.pairing w (fun i=>if i∈X then 1 else 0) (signature H M U w)=_
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [RootedSignatureSpan.pairing_comm]
  change RootedSignatureSpan.pairing w (MixedRooted.signature H.2.2.2.val M U w)
    (MixedRooted.signature (graphs j).2.2.2.val M U w)=_
  rw [←MixedRooted.partition_attach_root]
  have hattach:=G.partition_attach_reindex_all (MixedInstance.finiteRootEquiv r)
    (graphs j).2.2.2.val r M U w
  rw [MixedInstance.finiteRootEquiv_root] at hattach
  change ((G.reindexVertex (MixedInstance.finiteRootEquiv r)).attach (graphs j).2.2.2.val (.inl PUnit.unit)).partition M U w=_
  rw [hattach,totalEvaluation_valid _ _ _ _ (MixedRootedCodeMachines.attach_valid _ _ hg.1 r.isLt),
    MixedRootedCodeMachines.evaluate_attach]

end MixedRootedRestriction
end PlanarHom
