import PlanarHom.IndexedRotationRowCuts

/-! Exact arithmetic decoding of the Bool-conjugated row convention. -/
noncomputable section
open Classical
namespace PlanarHom.IndexedRotationCertificate
open MultiGraph MultiGraph.Kasteleyn RadialPotts.Assembly PlanarityLRRealization

def keepPrefix (m k : ℕ) (a : Dart (Fin m)) : Option (Dart (Fin k)) :=
  if h:a.1.val<k then some (⟨a.1.val,h⟩,a.2) else none

def decodeRaw (m : ℕ) (hm : 0<m) (d : ℕ) : Dart (Fin m) :=
  (faceIndex m).symm ⟨d%(2*m),Nat.mod_lt _ (by omega)⟩

theorem faceIndex_symm_value {m : ℕ} (d : Fin (2*m)) :
    ((faceIndex m).symm d).1.val=d.val/2 ∧ ((faceIndex m).symm d).2=decide (d.val%2=0) := by
  obtain ⟨⟨e,b⟩,rfl⟩:=(faceIndex m).surjective d
  simp only [Equiv.symm_apply_apply]
  cases b <;> simp [faceIndex,reversePerm,dartIndexEquiv_val,dartIndex] <;> omega

theorem decodeRaw_value (m : ℕ) (hm : 0<m) (d : ℕ) (hd : d<2*m) :
    (decodeRaw m hm d).1.val=d/2 ∧ (decodeRaw m hm d).2=decide (d%2=0) := by
  simpa only [decodeRaw,Nat.mod_eq_of_lt hd] using
    faceIndex_symm_value (⟨d%(2*m),Nat.mod_lt _ (by omega)⟩ : Fin (2*m))

theorem keepPrefix_decodeRaw (m k : ℕ) (hm : 0<m) (d : ℕ) (hd : d<2*m) :
    (keepPrefix m k (decodeRaw m hm d)).map (fun a=>(a.1.val,a.2))=
      if d/2<k then some (d/2,decide (d%2=0)) else none := by
  have hh:=decodeRaw_value m hm d hd
  simp only [keepPrefix,hh.1]
  split_ifs <;> simp [hh.2]

theorem filter_decodeRaw (m k : ℕ) (hm : 0<m) (xs : List ℕ)
    (hb : ∀d∈xs,d<2*m) :
    (((xs.map (decodeRaw m hm)).filterMap (keepPrefix m k)).map (fun a=>(a.1.val,a.2)))=
      (xs.filter (fun d=>decide (d/2<k))).map (fun d=>(d/2,decide (d%2=0))) := by
  rw [List.map_filterMap,List.filterMap_map]
  induction xs with
  | nil => rfl
  | cons d xs ih =>
    have hd:=hb d (by simp)
    have hxs : ∀a∈xs,a<2*m := fun a ha=>hb a (by simp [ha])
    simp only [List.filterMap_cons,Function.comp_apply,keepPrefix_decodeRaw m k hm d hd]
    by_cases hk : d/2<k
    · simp [hk,ih hxs]
    · simp [hk,ih hxs]

theorem decodeRaw_closing (m : ℕ) (hm : 0<m) (P : Equiv.Perm (Fin (2*m))) (q : Fin (2*m)) :
    decodeRaw m hm (flip m (P.symm q)).val=closingDart P q := by
  unfold decodeRaw
  simp only [Nat.mod_eq_of_lt (flip m (P.symm q)).isLt,Fin.eta]
  apply (faceIndex m).injective
  rw [Equiv.apply_symm_apply]
  change flip m (P.symm q)=dartIndexEquiv m (reversePerm (Fin m) ((dartIndexEquiv m).symm (P.symm q)))
  conv_lhs => rw [←Equiv.apply_symm_apply (dartIndexEquiv m) (P.symm q)]
  exact flip_index m _ _

end PlanarHom.IndexedRotationCertificate
