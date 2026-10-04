import PlanarHom.ColoredSignatureFieldMap
import PlanarHom.PlanarTransport

/-! NEW reconstruction. Only internal/occurrence labels are renamed. Terminals
remain fixed; the actual plane subset and complete colored assignment sum agree. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.TwoTerminal
variable {J E J' E' C R : Type} [Fintype J] [Fintype E]
    [Fintype J'] [Fintype E'] [Fintype C] [CommSemiring R]

def reindexInternal (G : TwoTerminal J E) (v : J ≃ J') (e : E ≃ E') : TwoTerminal J' E' :=
  G.reindex (Equiv.sumCongr (Equiv.refl Bool) v) e

theorem reindexInternal_planar (G : TwoTerminal J E) (v : J ≃ J') (e : E ≃ E')
    (hG : PlanarEdgeGadget G) : PlanarEdgeGadget (G.reindexInternal v e) := by
  obtain ⟨d,hd⟩ := hG
  let he := G.reindexEquiv (Equiv.sumCongr (Equiv.refl Bool) v) e
  refine ⟨d.transport he,?_⟩
  exact (d.outerCofacial_transport_iff he (Sum.inl false) (Sum.inl true)).mpr hd

theorem coloredSignature_reindexInternal (G : TwoTerminal J E) (v : J ≃ J') (e : E ≃ E')
    (W : E → Matrix C C R) (w : C → R) :
    coloredSignature (G.reindexInternal v e) (fun f => W (e.symm f)) w =
      coloredSignature G W w := by
  classical
  funext i j
  unfold coloredSignature
  apply Fintype.sum_equiv (v.symm.arrowCongr (Equiv.refl C))
  intro η
  have hext (z : Bool ⊕ J) :
      extend i j η ((Equiv.sumCongr (Equiv.refl Bool) v) z) =
        extend i j (fun z => η (v z)) z := by
    cases z with
    | inl z => cases z <;> rfl
    | inr z => rfl
  change (∏ z : J',w (η z)) *
      (∏ f : E',W (e.symm f) (extend i j η ((Equiv.sumCongr (Equiv.refl Bool) v) (G.src (e.symm f))))
        (extend i j η ((Equiv.sumCongr (Equiv.refl Bool) v) (G.dst (e.symm f))))) = _
  simp only [hext]
  rw [←v.prod_comp (fun z => w (η z)), ←e.prod_comp
    (fun f => W (e.symm f) (extend i j (fun z => η (v z)) (G.src (e.symm f)))
      (extend i j (fun z => η (v z)) (G.dst (e.symm f))))]
  simp
  rfl

end PlanarHom.TwoTerminal
