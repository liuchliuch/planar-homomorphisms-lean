import PlanarHom.FisherContourOrdering

/-! NEW canonical occurrence scan interpreted as a complete typed Fisher
incidence ordering. Both tags of a loop remain distinct list entries. -/
noncomputable section
open Classical
namespace PlanarHom.FisherCubicCode
open Complexity MultiGraph Fisher PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)

 def scanDarts : List (Fin g.edges.length×Bool) :=
  (List.finRange g.edges.length).flatMap (fun e=>[(e,false),(e,true)])

 theorem scanDarts_mem (a : Fin g.edges.length×Bool) : a∈scanDarts g := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [scanDarts]

 theorem scanDarts_nodup : (scanDarts g).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun e _=>by simp,?_⟩
  apply (List.nodup_finRange _).imp
  intro e f hef a ha hb
  have he:a.1=e:=by rcases List.mem_cons.mp ha with h | h; exact congrArg Prod.fst h; simpa using congrArg Prod.fst (List.mem_singleton.mp h)
  have hf:a.1=f:=by rcases List.mem_cons.mp hb with h | h; exact congrArg Prod.fst h; simpa using congrArg Prod.fst (List.mem_singleton.mp h)
  exact hef (he.symm.trans hf)

 def typedRow (v : Fin g.vertices) : List (Fin g.edges.length×Bool) :=
  (scanDarts g).filter (fun a=>decide ((g.toMultiGraph hg).dartVertex a=v))

 theorem typedRow_nodup (v : Fin g.vertices) : (typedRow g hg v).Nodup := (scanDarts_nodup g).filter _
 theorem mem_typedRow (v : Fin g.vertices) (a : Fin g.edges.length×Bool) :
    a∈typedRow g hg v ↔ (g.toMultiGraph hg).dartVertex a=v := by
  simp [typedRow,scanDarts_mem]

 theorem zipIdx_eq : g.edges.zipIdx=(List.finRange g.edges.length).map (fun e=>(g.edges.get e,e.val)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

 theorem typedRow_erase (v : Fin g.vertices) : (typedRow g hg v).map eraseDart=row g v.val := by
  simp only [typedRow,scanDarts,List.filter_flatMap,List.map_flatMap]
  rw [row,zipIdx_eq,List.flatMap_map]
  congr 1
  funext e
  have hs : (g.toMultiGraph hg).src e=v ↔ (g.edges.get e).1=v.val := Fin.ext_iff
  have ht : (g.toMultiGraph hg).dst e=v ↔ (g.edges.get e).2.1=v.val := Fin.ext_iff
  simp [List.filter_cons,dartVertex,hs,ht,eraseDart,List.get_eq_getElem]
  split_ifs <;> rfl

 def ordering : (g.toMultiGraph hg).IncidenceOrdering where
  degree v := (typedRow g hg v).length
  atVertex v := (List.Nodup.getEquiv (typedRow g hg v) (typedRow_nodup g hg v)).trans
    { toFun := fun a=>⟨a.val,(mem_typedRow g hg v a.val).mp a.property⟩
      invFun := fun a=>⟨a.val,(mem_typedRow g hg v a.val).mpr a.property⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }

 theorem ordering_realizes : FisherContourOrder.Realizes g hg
    ((List.range g.vertices).map (row g)) (ordering g hg) := by
  intro v
  simp only [FisherExpansionCode.row,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range v.isLt,Option.map_some,Option.getD_some]
  change row g v.val=(List.ofFn (typedRow g hg v).get).map eraseDart
  rw [List.ofFn_get,typedRow_erase]

 theorem ordering_degree (v : Fin g.vertices) :
    (ordering g hg).degree v=(row g v.val).length := by
  have hh:=congrArg List.length (typedRow_erase g hg v)
  simpa [ordering] using hh

 def ports (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3) :
    (Fin g.vertices×Fin 3)≃(Fin g.edges.length×Bool) :=
  ((Equiv.sigmaEquivProd (Fin g.vertices) (Fin 3)).symm.trans
    (Equiv.sigmaCongrRight (fun v=>finCongr ((ordering g hg).degree_eq v |>.trans (hc v)).symm))).trans
      (ordering g hg).darts

 theorem ports_vertex (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3)
    (a : Fin g.edges.length×Bool) : ((ports g hg hc).symm a).1=(g.toMultiGraph hg).dartVertex a := by
  exact (ordering g hg).darts_symm_vertex a

 theorem cubicOriginal_ports (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3) :
    cubicOriginal (ports g hg hc)=g.toMultiGraph hg := by
  apply congrArg₂ MultiGraph.mk
  · funext e
    exact ports_vertex g hg hc (e,false)
  · funext e
    exact ports_vertex g hg hc (e,true)

end PlanarHom.FisherCubicCode
