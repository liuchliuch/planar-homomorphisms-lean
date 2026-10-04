import PlanarHom.FisherCubicRotation

/-! NEW explicit three-dart formula for the inherited triangle row, in the
arbitrary canonical cubic port enumeration used by the numeric compiler. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype E] [DecidableEq (Dart E)]
variable (p : (V×Fin 3)≃(E×Bool)) (R : RotationRows (cubicOriginal p))

 theorem cubic_internal_dart_of_host (d : Dart (E⊕(V×Fin 3))) (v : V) (i k : Fin 3)
    (he : d.1=.inr (v,k)) (hh : ((cubicDecoration p).dartPair d).1=(v,i)) :
    d=(.inr (v,k),decide (triangle.src k=i)) := by
  rcases d with ⟨e,b⟩
  dsimp only at he
  subst e
  have hs := congrArg Prod.snd hh
  cases b
  · have hd : triangle.dst k=i := hs
    have hn : triangle.src k≠i := by rw [←hd]; exact triangle_distinct_endpoints k
    simp [hn]
  · have hd : triangle.src k=i := hs
    simp [hd]

 theorem cubicInheritedRows_row (q : V×Fin 3) :
    let a := reversePerm E (p q)
    let j := (p.symm (reversePerm E (R.rotation a))).2
    let k := (p.symm (reversePerm E (R.rotation.symm a))).2
    (cubicInheritedRows p R).row q=
      [(.inl a.1,a.2),(.inr (q.1,k),decide (triangle.src k=q.2)),
        (.inr (q.1,j),decide (triangle.src j=q.2))] := by
  let a := reversePerm E (p q)
  let j := (cubicVertexEquiv p (R.rotation a)).2
  let k := (cubicVertexEquiv p (R.rotation.symm a)).2
  change (cubicInheritedRows p R).row q=
    [(.inl a.1,a.2),(.inr (q.1,k),decide (triangle.src k=q.2)),
      (.inr (q.1,j),decide (triangle.src j=q.2))]
  have ha : (cubicVertexEquiv p).symm q=a := rfl
  have haq : cubicVertexEquiv p a=q := by rw [←ha,(cubicVertexEquiv p).apply_symm_apply]
  have hthree := (rotation_three R (cubic_row_length p R) a).1
  have hsq : R.rotation (R.rotation a)=R.rotation.symm a := by
    apply R.rotation.eq_symm_apply.mpr
    simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply] using hthree
  have hk : cubicCornerEquiv p R a=(q.1,k) := by
    apply Prod.ext
    · exact (cubicCorner_first p R a).trans (show (cubicVertexEquiv p a).1=q.1 from congrArg (fun x : V×Fin 3=>x.1) haq)
    · change (cubicVertexEquiv p (R.rotation (R.rotation a))).2=k
      rw [hsq]
  have hj : cubicCornerEquiv p R (R.rotation.symm a)=(q.1,j) := by
    apply Prod.ext
    · change (cubicVertexEquiv p (R.rotation (R.rotation (R.rotation.symm a)))).1=q.1
      rw [R.rotation.apply_symm_apply,cubicVertexEquiv_next_host,haq]
    · change (cubicVertexEquiv p (R.rotation (R.rotation (R.rotation.symm a)))).2=j
      rw [R.rotation.apply_symm_apply]
  have hext : cubicDartEquiv p R (polygonExternal a)=(.inl a.1,a.2) := by
    simp only [cubicDartEquiv,twistedDartEquiv,Equiv.coe_fn_mk,cubicEdgeEquiv,Equiv.sumCongr_apply,
      polygonExternal,Sum.map_inl,Equiv.refl_apply,cubicEdgeFlip,Sum.elim_inl,Bool.xor_false]
  have hout : cubicDartEquiv p R (polygonOutgoing a)=
      (.inr (q.1,k),decide (triangle.src k=q.2)) := by
    apply cubic_internal_dart_of_host p _ q.1 q.2 k
    · change Sum.inr (cubicCornerEquiv p R a)=Sum.inr (q.1,k)
      rw [hk]
    · rw [cubicDart_host,polygonOutgoing_host,haq]
  have hin : cubicDartEquiv p R (polygonIncoming R a)=
      (.inr (q.1,j),decide (triangle.src j=q.2)) := by
    apply cubic_internal_dart_of_host p _ q.1 q.2 j
    · change Sum.inr (cubicCornerEquiv p R (R.rotation.symm a))=Sum.inr (q.1,j)
      rw [hj]
    · rw [cubicDart_host,polygonIncoming_host,haq]
  change (polygonRow R ((cubicVertexEquiv p).symm q)).map (cubicDartEquiv p R)=_
  rw [ha,polygonRow,List.map_cons,List.map_cons,List.map_cons,List.map_nil,hext,hout,hin]

end PlanarHom.Fisher
