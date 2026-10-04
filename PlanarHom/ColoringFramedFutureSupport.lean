import PlanarHom.ColoringFramedMarkerInjection

/-! NEW exact future-patch support and actual old/new face separation for the
canonical face-splice program. Input origins are the proved registry origins. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree
open PlanarityLRRealization FinitePermutationCycles

 theorem patchDart_index_eq (f:NumericFormula) (i j:Canvas.Index f)
    (a:MultiGraph.Kasteleyn.Dart (PatchEdge f i)) (b:MultiGraph.Kasteleyn.Dart (PatchEdge f j))
    (h:patchDart f i a=patchDart f j b) : i=j :=
  congrArg Sigma.fst (Sum.inr.inj (congrArg Prod.fst h))

 theorem oldMarker_ne_patch (f:NumericFormula) (hf:NumericValid f) (i:Canvas.Index f)
    (t:Fin (sharedPred f i+1)) (j:Canvas.Index f) (hij:i.val≤j.val)
    (a:MultiGraph.Kasteleyn.Dart (PatchEdge f j)) : oldMarker f hf i t≠patchDart f j a := by
  let p:=FramedMacro.leftPort (canvasCell f i).shape (sharedIndex f i t)
  have hp:p.1∈(canvasCell f i).shape.leftPorts:=FramedMacro.leftPort_mem _ _
  change producerMarker f hf (Canvas.port f i p)≠_
  intro he
  rcases Canvas.input_origin f hf i p.1 hp with ⟨v,hv⟩ | ⟨c,o,hci,hco⟩
  · simp only [producerMarker,Canvas.port,hv] at he
    exact Sum.inl_ne_inr (congrArg Prod.fst he)
  · simp only [producerMarker,Canvas.port,hco] at he
    have hh:=congrArg Fin.val (patchDart_index_eq f c j _ _ he)
    omega

 theorem newMarker_ne_patch (f:NumericFormula) (i:Canvas.Index f) (t:Fin (sharedPred f i+1))
    (j:Canvas.Index f) (hij:i≠j) (a:MultiGraph.Kasteleyn.Dart (PatchEdge f j)) :
    newMarker f i t≠patchDart f j a := fun h=>hij (patchDart_index_eq f i j _ _ h)

 theorem oldMarker_ne_newMarker (f:NumericFormula) (hf:NumericValid f) (i:Canvas.Index f)
    (s t:Fin (sharedPred f i+1)) : oldMarker f hf i s≠newMarker f i t :=
  oldMarker_ne_patch f hf i s i (le_refl _) _

 theorem prefixFace_patch_future (f:NumericFormula) (hf:NumericValid f) (k:ℕ)
    (j:Canvas.Index f) (hkj:k≤j.val) (a:MultiGraph.Kasteleyn.Dart (PatchEdge f j)) :
    prefixFace f hf k (patchDart f j a)=
      patchDart f j ((FramedMacro.rows (canvasCell f j).shape).facePerm a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk:k<(canvas f).length:=by have hj:=j.isLt;omega
    let i:Canvas.Index f:=⟨k,hk⟩
    rw [prefixFace,dif_pos hk]
    change spliceCell f hf (prefixFace f hf k) i (patchDart f j a)=_
    unfold spliceCell
    rw [splicePrefix_untouched]
    · exact ih (by omega)
    · intro t ht
      have hx:extendBoundaryPath (sharedPred f i) (oldMarker f hf i) t=oldMarker f hf i ⟨t,ht⟩:=
        extendBoundaryPath_at _ _ ⟨t,ht⟩
      have hy:extendBoundaryPath (sharedPred f i) (newMarker f i) t=newMarker f i ⟨t,ht⟩:=
        extendBoundaryPath_at _ _ ⟨t,ht⟩
      rw [hx,hy]
      exact ⟨(oldMarker_ne_patch f hf i ⟨t,ht⟩ j (by change k≤j.val;omega) a).symm,
        (newMarker_ne_patch f i ⟨t,ht⟩ j (by intro he;have hh:=congrArg Fin.val he;change k=j.val at hh;omega) a).symm⟩

 theorem prefixFace_patch_iterate_future (f:NumericFormula) (hf:NumericValid f) (k:ℕ)
    (j:Canvas.Index f) (hkj:k≤j.val) (a:MultiGraph.Kasteleyn.Dart (PatchEdge f j)) (t:ℕ) :
    (prefixFace f hf k)^[t] (patchDart f j a)=
      patchDart f j (((FramedMacro.rows (canvasCell f j).shape).facePerm)^[t] a) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih,prefixFace_patch_future f hf k j hkj,Function.iterate_succ_apply']

 theorem prefixFace_old_new_not_sameCycle (f:NumericFormula) (hf:NumericValid f) (i:Canvas.Index f) :
    ¬(prefixFace f hf i.val).SameCycle (oldMarker f hf i 0) (newMarker f i 0) := by
  intro h
  obtain ⟨t,ht⟩:=h.symm.exists_nat_pow_eq
  rw [←Equiv.Perm.iterate_eq_pow] at ht
  change (prefixFace f hf i.val)^[t] (patchDart f i _)=oldMarker f hf i 0 at ht
  rw [prefixFace_patch_iterate_future f hf i.val i (le_refl _)] at ht
  exact oldMarker_ne_patch f hf i 0 i (le_refl _) _ ht.symm

end PlanarHom.ColoringEmitter.FramedCanvas
