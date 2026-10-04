import PlanarHom.HomogeneousSourceOrientationComponents
import PlanarHom.FixedRealMixedSupportRestriction

/-! Intrinsic bipartition metadata for a retained mixed language. Ordinary
unaries occupy labels below u; the two reserved labels are u and u+1. Component
extraction may reorder metadata, but preserves every ordinary unary occurrence. -/
noncomputable section
open Classical
namespace PlanarHom.MixedOrientation
open Complexity Complexity.MixedCode PrescribedDomains GraphComponentCode
open HomogeneousSourceOrientation
variable {b u:ℕ}

def strip (u:ℕ) (g:MixedCode) : MixedCode :=
  ⟨g.vertices,g.edges,g.unaries.filter (fun a=>decide (a.2<u))⟩

def Tags (u:ℕ) (g:MixedCode) (δ:Fin g.vertices→Fin 2) : Prop :=
  g.unaries.Perm ((strip u g).unaries++domainOccurrences (unaryTypes:=u) g δ)

def Proper (g:MixedCode) (hg:g.Valid b (u+2)) (δ:Fin g.vertices→Fin 2) : Prop :=
  ∀a,∀ha:a∈g.edges,δ ⟨a.1,(hg.1 a ha).1⟩≠δ ⟨a.2.1,(hg.1 a ha).2.1⟩

def Tagged (b u:ℕ) (g:MixedCode) : Prop :=
  ∃hg:g.PlanarValid b (u+2),∃δ:Fin g.vertices→Fin 2,Tags u g δ ∧ Proper g hg.1 δ

def ConnectedTagged (b u:ℕ) (g:MixedCode) : Prop :=
  Tagged b u g ∧ (support g).Connected ∧ 0<g.vertices

theorem strip_valid (g:MixedCode) (hg:g.Valid b (u+2)) : (strip u g).Valid b u := by
  refine ⟨hg.1,?_⟩
  intro a ha
  have h:=List.mem_filter.mp ha
  exact ⟨(hg.2 a h.1).1,of_decide_eq_true h.2⟩

theorem strip_withDomains (g:MixedCode) (hg:g.Valid b u) (δ:Fin g.vertices→Fin 2) :
    strip u (withDomains (unaryTypes:=u) g δ)=g := by
  have ho:g.unaries.filter (fun a=>decide (a.2<u))=g.unaries:=by
    apply List.filter_eq_self.mpr
    intro a ha
    exact decide_eq_true (hg.2 a ha).2
  have hd:(domainOccurrences (unaryTypes:=u) g δ).filter (fun a=>decide (a.2<u))=[]:=by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp ha
    simp
  cases g
  simp only [strip,withDomains,List.filter_append,ho,hd,List.append_nil]

theorem tags_withDomains (g:MixedCode) (hg:g.Valid b u) (δ:Fin g.vertices→Fin 2) :
    Tags u (withDomains (unaryTypes:=u) g δ) δ := by
  unfold Tags
  rw [strip_withDomains g hg δ]
  exact List.Perm.refl _

theorem strip_extract (g:MixedCode) (xs:List ℕ) : strip u (extract g xs)=extract (strip u g) xs := by
  unfold strip extract
  congr 1
  simp only [List.filter_map,List.filter_filter]
  congr 1
  apply List.filter_congr
  intro a ha
  simp only [Function.comp_apply]
  exact Bool.and_comm _ _

theorem domains_nodup (g:MixedCode) (δ:Fin g.vertices→Fin 2) :
    (domainOccurrences (unaryTypes:=u) g δ).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j he
  exact Fin.ext (congrArg Prod.fst he)

theorem domain_extract_perm (g:MixedCode) (δ:Fin g.vertices→Fin 2) (xs:List ℕ)
    (hx:xs.Nodup) (hb:∀v∈xs,v<g.vertices) :
    (((domainOccurrences (unaryTypes:=u) g δ).filter (fun a=>decide (a.1∈xs))).map
      (fun a=>(xs.idxOf a.1,a.2))).Perm
      (domainOccurrences (unaryTypes:=u) (extract g xs) (fun v=>δ (localVertex g xs hb v))) := by
  have hn:((((domainOccurrences (unaryTypes:=u) g δ).filter (fun a=>decide (a.1∈xs))).map
      (fun a=>(xs.idxOf a.1,a.2)))).Nodup := by
    apply List.Nodup.map_on ?_ ((domains_nodup g δ).filter _)
    intro a ha z hz he
    have ha':a.1∈xs:=of_decide_eq_true (List.mem_filter.mp ha).2
    have hz':z.1∈xs:=of_decide_eq_true (List.mem_filter.mp hz).2
    have hh:=Prod.mk.inj he
    exact Prod.ext ((List.idxOf_inj ha' hz').mp hh.1) hh.2
  apply (List.perm_ext_iff_of_nodup hn (domains_nodup _ _)).mpr
  intro a
  constructor
  · intro ha
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp ha
    obtain ⟨hz,hzi⟩:=List.mem_filter.mp hz
    have hzi':z.1∈xs:=of_decide_eq_true hzi
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hz
    apply List.mem_ofFn.mpr
    refine ⟨⟨xs.idxOf i.val,List.idxOf_lt_length_iff.mpr hzi'⟩,?_⟩
    simp only [localVertex_index g xs hb i hzi']
  · intro ha
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp ha
    apply List.mem_map.mpr
    refine ⟨((localVertex g xs hb v).val,u+(δ (localVertex g xs hb v)).val),?_,?_⟩
    · exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨localVertex g xs hb v,rfl⟩,
        decide_eq_true (List.get_mem xs v)⟩
    · change (xs.idxOf (xs.get v),_)=_
      rw [List.get_idxOf hx v]

theorem tags_extract (g:MixedCode) (δ:Fin g.vertices→Fin 2) (ht:Tags u g δ)
    (xs:List ℕ) (hx:xs.Nodup) (hb:∀v∈xs,v<g.vertices) :
    Tags u (extract g xs) (fun v=>δ (localVertex g xs hb v)) := by
  have hp:=(ht.filter (fun a=>decide (a.1∈xs))).map (fun a=>(xs.idxOf a.1,a.2))
  simp only [List.filter_append,List.map_append] at hp
  unfold Tags
  rw [strip_extract]
  exact hp.trans (List.Perm.append_left _ (domain_extract_perm g δ xs hx hb))

theorem proper_extract (g:MixedCode) (hg:g.Valid b (u+2)) (δ:Fin g.vertices→Fin 2)
    (hp:Proper g hg δ) (xs:List ℕ) (hb:∀v∈xs,v<g.vertices) :
    Proper (extract g xs) (extract_valid g hg xs) (fun v=>δ (localVertex g xs hb v)) := by
  intro a ha
  obtain ⟨z,hz,rfl⟩:=List.mem_map.mp ha
  obtain ⟨hz,hzi⟩:=List.mem_filter.mp hz
  have hzi':z.1∈xs ∧z.2.1∈xs:=of_decide_eq_true hzi
  have h:=hp z hz
  change δ (localVertex g xs hb _)≠δ (localVertex g xs hb _)
  rw [localVertex_index g xs hb ⟨z.1,(hg.1 z hz).1⟩ hzi'.1,
    localVertex_index g xs hb ⟨z.2.1,(hg.1 z hz).2.1⟩ hzi'.2]
  exact h

theorem components_tagged (g:MixedCode) (hg:Tagged b u g) (c:MixedCode) (hc:c∈components g) :
    ConnectedTagged b u c := by
  obtain ⟨hp,δ,ht,hproper⟩:=hg
  have hm:=components_promises g hp c hc
  obtain ⟨xs,hxs,rfl⟩:=List.mem_map.mp hc
  refine ⟨⟨hm.1,fun v=>δ (localVertex g xs (part_vertex_lt g xs hxs) v),?_,?_⟩,hm.2⟩
  · exact tags_extract g δ ht xs (part_nodup g xs hxs) (part_vertex_lt g xs hxs)
  · exact proper_extract g hp.1 δ hproper xs (part_vertex_lt g xs hxs)

end PlanarHom.MixedOrientation
