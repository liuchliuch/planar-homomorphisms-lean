import PlanarHom.FixedGadgetNetworkCode
import PlanarHom.PrescribedDomainQueryPromises

/-! Exact prescribed-domain metadata through arbitrary typed template networks.
Old unary companions stay in their original order, and every private vertex
receives exactly one reserved intrinsic occurrence. Binary endpoint permissions
are arbitrary ordered tables; in particular same-side companions are allowed. -/
noncomputable section
open Classical
namespace PlanarHom.TypedGadgetAppend
open Complexity PrescribedDomains FixedGadgetNetwork
variable {bt ut dt : ℕ}

/-- A canonical intrinsic tail, indexed by actual allocated vertices. -/
def domains (ut n : ℕ) (tag : ℕ → Fin dt) : List (ℕ × ℕ) :=
  (List.range n).map (fun v => (v,ut+(tag v).val))

/-- The fixed template has no boundary indicator and exactly one private
indicator. Its edge typing may depend on the permitted boundary domains. -/
structure TemplateTyping (B : Fin bt → Fin dt → Fin dt → Prop)
    (t : Template) (tag : ℕ → Fin dt) : Prop where
  valid : t.code.Valid bt (ut+dt)
  domains : t.unaries = (List.range t.privateCount).map
    (fun j => (t.boundary+j,ut+(tag (t.boundary+j)).val))
  edges : ∀ e (he : e∈t.edges), B ⟨e.2.2,(valid.1 e he).2.2⟩ (tag e.1) (tag e.2.1)

/-- A literal intermediate code, including all old ordinary unary companions. -/
structure Tagged (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (ordinary : List (ℕ × ℕ))
    (g : MixedCode) (tag : ℕ → Fin dt) : Prop where
  valid : g.Valid bt (ut+dt)
  domains : g.unaries = ordinary ++ domains ut g.vertices tag
  edges : ∀ e (he : e∈g.edges), B ⟨e.2.2,(valid.1 e he).2.2⟩ (tag e.1) (tag e.2.1)
  ordinary_valid : ∀ u∈ordinary, u.1<g.vertices ∧ u.2<ut
  ordinary_typed : ∀ u (hu : u∈ordinary), T ⟨u.2,(ordinary_valid u hu).2⟩ (tag u.1)

def attachTags (g : MixedCode) (t : Template) (old fresh : ℕ → Fin dt) : ℕ → Fin dt :=
  fun v => if v<g.vertices then old v else fresh (t.boundary+(v-g.vertices))

@[simp] theorem attachTags_old (g : MixedCode) (t : Template) (old fresh : ℕ → Fin dt)
    (v : ℕ) (hv : v<g.vertices) : attachTags g t old fresh v=old v := if_pos hv

@[simp] theorem attachTags_new (g : MixedCode) (t : Template) (old fresh : ℕ → Fin dt)
    (j : ℕ) : attachTags g t old fresh (g.vertices+j)=fresh (t.boundary+j) := by
  simp [attachTags]

theorem attachTags_remap (g : MixedCode) (t : Template) (old fresh : ℕ → Fin dt)
    (ports : List ℕ) (hp : ports.length=t.boundary) (hr : ∀v∈ports,v<g.vertices)
    (hboundary : ∀v,v<t.boundary → old (ports.getD v 0)=fresh v)
    (v : ℕ) (_hv : v<t.boundary+t.privateCount) :
    attachTags g t old fresh (remapVertex t g.vertices ports v)=fresh v := by
  unfold remapVertex
  split_ifs with h
  · have hvl : v<ports.length := by omega
    have hm : ports.getD v 0∈ports := by
      rw [List.getD_eq_getElem _ _ hvl]
      exact List.getElem_mem hvl
    rw [attachTags_old _ _ _ _ _ (hr _ hm),hboundary v h]
  · rw [attachTags_new]
    congr 1
    omega

theorem domains_attach (g : MixedCode) (t : Template) (old fresh : ℕ → Fin dt) :
    domains ut (g.vertices+t.privateCount) (attachTags g t old fresh)=
      domains ut g.vertices old ++ (List.range t.privateCount).map
        (fun j => (g.vertices+j,ut+(fresh (t.boundary+j)).val)) := by
  unfold domains
  rw [List.range_add,List.map_append,List.map_map]
  congr 1
  · apply List.map_congr_left
    intro v hv
    rw [attachTags_old _ _ _ _ _ (List.mem_range.mp hv)]
  · apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply,attachTags_new]

theorem Tagged.attach {B : Fin bt → Fin dt → Fin dt → Prop}
    {T : Fin ut → Fin dt → Prop} {ordinary : List (ℕ × ℕ)}
    {g : MixedCode} {old : ℕ → Fin dt} (hg : Tagged B T ordinary g old)
    {t : Template} {fresh : ℕ → Fin dt} (ht : TemplateTyping (ut:=ut) B t fresh)
    (ports : List ℕ) (hp : ports.length=t.boundary) (hr : ∀v∈ports,v<g.vertices)
    (hboundary : ∀v,v<t.boundary → old (ports.getD v 0)=fresh v) :
    Tagged B T ordinary (attachTemplate t g ports) (attachTags g t old fresh) := by
  refine ⟨attachTemplate_valid t g ports ht.valid hg.valid hp hr,?_,?_,?_,?_⟩
  · change g.unaries ++ t.unaries.map (remapUnary t g.vertices ports)=_
    rw [hg.domains,ht.domains,List.map_map]
    rw [show (attachTemplate t g ports).vertices=g.vertices+t.privateCount from rfl,
      domains_attach,List.append_assoc]
    congr 2
    apply List.map_congr_left
    intro j _
    simp [remapUnary,remapVertex]
  · intro e he
    rcases List.mem_append.mp he with he|he
    · rw [attachTags_old _ _ _ _ _ (hg.valid.1 e he).1,
        attachTags_old _ _ _ _ _ (hg.valid.1 e he).2.1]
      exact hg.edges e he
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
      have hav := ht.valid.1 a ha
      change B _ (attachTags g t old fresh (remapVertex t g.vertices ports a.1))
        (attachTags g t old fresh (remapVertex t g.vertices ports a.2.1))
      rw [attachTags_remap g t old fresh ports hp hr hboundary a.1 hav.1,
        attachTags_remap g t old fresh ports hp hr hboundary a.2.1 hav.2.1]
      exact ht.edges a ha
  · intro u hu
    exact ⟨(hg.ordinary_valid u hu).1.trans_le (Nat.le_add_right _ _),(hg.ordinary_valid u hu).2⟩
  · intro u hu
    rw [attachTags_old _ _ _ _ _ (hg.ordinary_valid u hu).1]
    exact hg.ordinary_typed u hu

/-- The exact output promise, with the same ordinary occurrence list. -/
theorem Tagged.encodedGraph {B : Fin bt → Fin dt → Fin dt → Prop}
    {T : Fin ut → Fin dt → Prop} {ordinary : List (ℕ × ℕ)}
    {g : MixedCode} {tag : ℕ → Fin dt} (hg : Tagged B T ordinary g tag)
    (hp : g.underlying.PlanarValid) : EncodedGraph B T g := by
  let bare : MixedCode := ⟨g.vertices,g.edges,ordinary⟩
  have hb : bare.Valid bt ut := ⟨hg.valid.1,hg.ordinary_valid⟩
  have hd : TypedGadgetAppend.domains ut g.vertices tag = domainOccurrences (unaryTypes:=ut) bare (fun v=>tag v.val) := by
    apply List.ext_getElem
    · simp [TypedGadgetAppend.domains,domainOccurrences,bare]
    · intro i hi hj
      simp [TypedGadgetAppend.domains,domainOccurrences,bare]
  have he : g=withDomains (unaryTypes:=ut) bare (fun v=>tag v.val) := by
    have hu := hg.domains.trans (congrArg (ordinary ++ ·) hd)
    cases g
    exact congrArg (MixedCode.mk _ _) hu
  rw [he]
  exact encodedInput_encode_withDomains (hg:=hb) ⟨hg.edges,hg.ordinary_typed⟩ hp

/-- Folding genuine attachments preserves every old assignment, not merely
its side class. Template tags may vary with the actual host endpoints. -/
theorem compile_tagged (ts : List Template)
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (ordinary : List (ℕ × ℕ)) (shared : ℕ) (initial : ℕ → Fin dt)
    (as : List Gate)
    (hgates : ∀ a∈as,a.Valid ts shared)
    (htags : ∀ a∈as,∃ fresh,TemplateTyping (ut:=ut) B (gateTemplate ts a) fresh ∧
      ∀v,v<(gateTemplate ts a).boundary → initial (a.2.getD v 0)=fresh v)
    (g : MixedCode) (tag : ℕ → Fin dt) (hg : Tagged B T ordinary g tag)
    (hshared : shared≤g.vertices) (hretain : ∀v,v<shared → tag v=initial v) :
    ∃ finalTag,Tagged B T ordinary (compile ts ⟨g,as⟩) finalTag ∧
      ∀v,v<shared → finalTag v=initial v := by
  induction as generalizing g tag with
  | nil => exact ⟨tag,hg,hretain⟩
  | cons a as ih =>
    have ha := hgates a (by simp)
    obtain ⟨fresh,ht,hports⟩ := htags a (by simp)
    let next := attachTags g (gateTemplate ts a) tag fresh
    have hn : Tagged B T ordinary (compileStep ts g a) next := by
      apply hg.attach ht a.2 ha.2.1 (fun v hv=>(ha.2.2 v hv).trans_le hshared)
      intro v hv
      have hv' : v<a.2.length := by rw [ha.2.1]; exact hv
      have hm : a.2.getD v 0∈a.2 := by
        rw [List.getD_eq_getElem _ _ hv']
        exact List.getElem_mem hv'
      rw [hretain _ (ha.2.2 _ hm),hports v hv]
    have hnretain : ∀v,v<shared → next v=initial v := by
      intro v hv
      rw [show next v=tag v from attachTags_old _ _ _ _ _ (hv.trans_le hshared)]
      exact hretain v hv
    obtain ⟨out,hout,hkeep⟩ := ih (fun b hb=>hgates b (by simp [hb]))
      (fun b hb=>htags b (by simp [hb])) (compileStep ts g a) next hn
      (hshared.trans (Nat.le_add_right _ _)) hnretain
    exact ⟨out,hout,hkeep⟩

end PlanarHom.TypedGadgetAppend
