import PlanarHom.PlanarityDepthFirstSearchAncestors

/-! NEW reconstruction. Discovery paths and parent occurrence positions are
literal source data, including distinct parallel occurrences and root sentinels. -/
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity

def GoodPath (g : MixedCode) (path : List ℕ) : Prop :=
  path.Nodup ∧ ∀v∈path,v<g.vertices

def TaskParent (g : MixedCode) (t : Task) : Prop :=
  t.enter=true → if t.path=[] then t.edge=g.edges.length
    else (t.vertex,t.edge)∈neighbours g (t.path.headD g.vertices)

def DiscoveryParent (g : MixedCode) (r : Discovery) : Prop :=
  if r.ancestors=[] then r.treeEdge=g.edges.length
    else (r.vertex,r.treeEdge)∈neighbours g (r.ancestors.headD g.vertices)

 theorem neighbours_index_lt (g : MixedCode) (v : ℕ) {a : Arc} (ha : a∈neighbours g v) :
    a.2<g.edges.length := by
  obtain ⟨p,hp,ha⟩ := List.mem_flatMap.mp ha
  have hi := List.snd_lt_of_mem_zipIdx hp
  rcases (mem_incidence v p a).mp ha with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simpa using hi

 theorem neighbours_occurrence (g : MixedCode) (v : ℕ) {a : Arc} (ha : a∈neighbours g v) :
    ∃e, g.edges[a.2]?=some e ∧
      ((e.1=v ∧ e.2.1=a.1) ∨ (e.1=a.1 ∧ e.2.1=v)) := by
  obtain ⟨p,hp,ha⟩ := List.mem_flatMap.mp ha
  have hi := List.mem_zipIdx_iff_getElem?.mp hp
  rcases (mem_incidence v p a).mp ha with ⟨hv,rfl⟩ | ⟨hv,rfl⟩
  · exact ⟨p.1,hi,Or.inl ⟨hv,rfl⟩⟩
  · exact ⟨p.1,hi,Or.inr ⟨rfl,hv⟩⟩

structure SourceInvariant (g : MixedCode) (s : State) : Prop where
  work_parent : ∀t∈s.work,TaskParent g t
  work_path : ∀t∈s.work,GoodPath g t.path
  record_parent : ∀r∈s.discovered,DiscoveryParent g r
  record_path : ∀r∈s.discovered,GoodPath g r.ancestors

 theorem sourceInvariant_initial (g : MixedCode) : SourceInvariant g (initial g) := by
  constructor
  · intro t ht
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
    simp [TaskParent,enterTask]
  · intro t ht
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
    simp [GoodPath,enterTask]
  · simp [initial]
  · simp [initial]

 theorem sourceInvariant_step (g : MixedCode) (s : State)
    (hs : StackInvariant g s) (h : SourceInvariant g s) : SourceInvariant g (step g s) := by
  cases hw : s.work with
  | nil => simpa [step,hw] using h
  | cons t rest =>
    cases ht : t.enter with
    | false =>
      simp only [step,hw,ht,Bool.false_eq_true,↓reduceIte]
      exact ⟨fun t' ht'=>h.work_parent t' (by rw [hw]; exact List.mem_cons_of_mem _ ht'),
        fun t' ht'=>h.work_path t' (by rw [hw]; exact List.mem_cons_of_mem _ ht'),
        h.record_parent,h.record_path⟩
    | true =>
      by_cases hn : t.vertex<g.vertices ∧ t.vertex∉seen s
      · have hactive : GoodPath g s.active :=
          ⟨hs.active_nodup,fun v hv=>hs.goodSeen.2 v (hs.active_seen v hv)⟩
        have hvnot : t.vertex∉s.active := fun hv=>hn.2 (hs.active_seen _ hv)
        have hpath : GoodPath g (t.vertex::s.active) := by
          exact ⟨List.nodup_cons.mpr ⟨hvnot,hactive.1⟩,by
            intro v hv; rcases List.mem_cons.mp hv with rfl | hv
            · exact hn.1
            · exact hactive.2 v hv⟩
        have hpaths := hs.paths
        rw [hw] at hpaths
        have htp := (hpaths.enter_tail ht).1
        have hparent := h.work_parent t (by rw [hw]; exact List.mem_cons_self) ht
        rw [htp] at hparent
        simp only [step,hw,ht,hn,↓reduceIte]
        constructor
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
            simpa [TaskParent,enterTask] using hb
          · rcases List.mem_cons.mp ha with rfl | ha
            · simp [TaskParent,exitTask]
            · exact h.work_parent a (by rw [hw]; exact List.mem_cons_of_mem _ ha)
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
            exact hpath
          · rcases List.mem_cons.mp ha with rfl | ha
            · simp [GoodPath,exitTask]
            · exact h.work_path a (by rw [hw]; exact List.mem_cons_of_mem _ ha)
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hparent
          · exact h.record_parent r hr
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hactive
          · exact h.record_path r hr
      · simp only [step,hw,ht,hn,↓reduceIte]
        exact ⟨fun t' ht'=>h.work_parent t' (by rw [hw]; exact List.mem_cons_of_mem _ ht'),
          fun t' ht'=>h.work_path t' (by rw [hw]; exact List.mem_cons_of_mem _ ht'),
          h.record_parent,h.record_path⟩

 theorem sourceInvariant_iterate (g : MixedCode) (n : ℕ) :
    SourceInvariant g ((step g)^[n] (initial g)) := by
  induction n with
  | zero => exact sourceInvariant_initial g
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact sourceInvariant_step g _ (stackInvariant_iterate g n) ih

 theorem ancestors_nodup (g : MixedCode) {v : ℕ} (hv : v<g.vertices) : (ancestors g v).Nodup :=
  ((sourceInvariant_iterate g (fuel g)).record_path _ (discoveryAt_mem g hv).1).1

 theorem ancestors_valid (g : MixedCode) {v u : ℕ} (hv : v<g.vertices)
    (hu : u∈ancestors g v) : u<g.vertices :=
  ((sourceInvariant_iterate g (fuel g)).record_path _ (discoveryAt_mem g hv).1).2 u hu

 theorem root_parentEdge (g : MixedCode) {v : ℕ} (hv : v<g.vertices) (hroot : height g v=0) :
    parentEdge g v=g.edges.length := by
  have hh := (sourceInvariant_iterate g (fuel g)).record_parent _ (discoveryAt_mem g hv).1
  have he : (ancestors g v)=[] := List.length_eq_zero_iff.mp hroot
  change (discoveryAt g v).ancestors=[] at he
  simpa only [DiscoveryParent,he,↓reduceIte,parentEdge] using hh

 theorem parentEdge_incidence (g : MixedCode) {v : ℕ} (hv : v<g.vertices) (hroot : 0<height g v) :
    (v,parentEdge g v)∈neighbours g (parentVertex g v) := by
  have hh := (sourceInvariant_iterate g (fuel g)).record_parent _ (discoveryAt_mem g hv).1
  have he : (ancestors g v)≠[] := List.ne_nil_of_length_pos hroot
  have hv' := (discoveryAt_mem g hv).2
  change (discoveryAt g v).ancestors≠[] at he
  simpa only [DiscoveryParent,if_neg he,hv',parentEdge,parentVertex,ancestors] using hh

 theorem parentEdge_lt (g : MixedCode) {v : ℕ} (hv : v<g.vertices) (hroot : 0<height g v) :
    parentEdge g v<g.edges.length := neighbours_index_lt g _ (parentEdge_incidence g hv hroot)

 theorem parentVertex_ancestor (g : MixedCode) {v : ℕ} (hv : v<g.vertices) (hroot : 0<height g v) :
    parentVertex g v∈ancestors g v := by
  cases he : ancestors g v with
  | nil => simp [height,he] at hroot
  | cons a path => simp [parentVertex,he]

 theorem parentVertex_height_lt (g : MixedCode) {v : ℕ} (hv : v<g.vertices) (hroot : 0<height g v) :
    height g (parentVertex g v)<height g v :=
  ancestors_height_lt g hv (parentVertex_ancestor g hv hroot)


 theorem parentEdge_injective (g : MixedCode) {u v : ℕ}
    (hu : u<g.vertices) (hv : v<g.vertices) (hdu : 0<height g u) (hdv : 0<height g v)
    (he : parentEdge g u=parentEdge g v) : u=v := by
  obtain ⟨e,heu,huends⟩ := neighbours_occurrence g _ (parentEdge_incidence g hu hdu)
  obtain ⟨f,hev,hvends⟩ := neighbours_occurrence g _ (parentEdge_incidence g hv hdv)
  rw [he] at heu
  have hef : e=f := Option.some.inj (heu.symm.trans hev)
  subst f
  have hpu := parentVertex_height_lt g hu hdu
  have hpv := parentVertex_height_lt g hv hdv
  rcases huends with ⟨hup,hue⟩ | ⟨hue,hup⟩ <;>
    rcases hvends with ⟨hvp,hve⟩ | ⟨hve,hvp⟩
  · exact hue.symm.trans hve
  · have h1 : parentVertex g u=v := hup.symm.trans hve
    have h2 : parentVertex g v=u := hvp.symm.trans hue
    rw [h1] at hpu
    rw [h2] at hpv
    omega
  · have h1 : parentVertex g u=v := hup.symm.trans hve
    have h2 : parentVertex g v=u := hvp.symm.trans hue
    rw [h1] at hpu
    rw [h2] at hpv
    omega
  · exact hue.symm.trans hve

end PlanarHom.PlanarityDepthFirstSearch
