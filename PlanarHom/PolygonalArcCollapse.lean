import PlanarHom.SegmentCollapseData
import PlanarHom.PolygonalSegmentIncidence

/-!
# Finite reduction of an external polygonal arc to a straight segment

Each step collapses the first segment toward its next joint, fixes the compact
nonadjacent suffix, and preserves the adjacent radial segment as a set. Thus the
remaining chain stays exactly polygonal despite the nonlinear plane map.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.Polygonal.Chain
open MultiGraph

/-- A finite simple external polygonal arc reduces to a straight segment by
composing actual localized segment-collapse maps. The map stays injective on
any retained set meeting the arc only at its two ends. -/
theorem exists_straight_segment_of_collapse
    (collapse : ∀ {a b : Plane}, a ≠ b → ∀ K : Set Plane,
      IsCompact K → Disjoint K [a -[ℝ] b] → Nonempty (LocalizedSegmentCollapse a b K))
    {a z : Plane} (p : Chain Set.univ a z) (hp : p.IsSimple) (haz : a ≠ z)
    (S : Set Plane) (hcontact : ∀ w, w ∈ p.support → w ∈ S → w = a ∨ w = z) :
    ∃ F : C(Plane,Plane), ∃ c : Plane,
      Set.InjOn F S ∧ F a = c ∧ F z = z ∧ c ≠ z ∧
      ∀ w, w ∈ [c -[ℝ] z] → w ∈ F '' S → w = c ∨ w = z := by
  induction p generalizing S with
  | nil a ha => exact (haz rfl).elim
  | @cons a b z h q ih =>
      cases q with
      | nil b hb =>
          refine ⟨ContinuousMap.id _,a,fun _ _ _ _ heq => heq,rfl,rfl,haz,?_⟩
          intro w hw hS
          apply hcontact w
          · rw [support_cons]
            exact Or.inl hw
          · simpa only [ContinuousMap.coe_id,Set.image_id] using hS
      | @cons b c z k r =>
          have hq : (Chain.cons k r).IsSimple := hp.2.1
          have hbz : b ≠ z := ne_endpoints_of_simple_cons k r hq
          have hbnot : b ∉ r.support := simple_source_notMem_tail k r hq
          have hznot : z ∉ [a -[ℝ] b] := by
            intro hz
            exact hbz (hp.2.2 z hz (Chain.cons k r).target_mem_support).symm
          have hdis : Disjoint r.support [a -[ℝ] b] := by
            apply Set.disjoint_left.mpr
            intro w hw hfirst
            have heq := hp.2.2 w hfirst (by rw [support_cons]; exact Or.inr hw)
            exact hbnot (heq ▸ hw)
          obtain ⟨C⟩ := collapse hp.1 r.support r.isCompact_support hdis
          have hCF (w : Plane) (hw : w ∈ [a -[ℝ] b]) : C.map w = b := by
            exact ((C.fibers w b).mpr (Or.inr ⟨hw,right_mem_segment ℝ a b⟩)).trans C.target
          have hinj : Set.InjOn C.map S := by
            intro x hx y hy heq
            rcases (C.fibers x y).mp heq with hxy | ⟨hxf,hyf⟩
            · exact hxy
            · have hxa : x = a :=
                (hcontact x (by rw [support_cons]; exact Or.inl hxf) hx).resolve_right
                  (fun hxz => hznot (hxz ▸ hxf))
              have hya : y = a :=
                (hcontact y (by rw [support_cons]; exact Or.inl hyf) hy).resolve_right
                  (fun hyz => hznot (hyz ▸ hyf))
              exact hxa.trans hya.symm
          have hcfix : C.map c = c := C.fixed c r.source_mem_support
          have hzfix : C.map z = z := C.fixed z r.target_mem_support
          have hrtail : C.map '' r.support = r.support := by
            ext w
            constructor
            · rintro ⟨x,hx,rfl⟩
              rwa [C.fixed x hx]
            · intro hw
              exact ⟨w,hw,C.fixed w hw⟩
          have htail : C.map '' (Chain.cons k r).support = (Chain.cons k r).support := by
            rw [support_cons,Set.image_union,C.ray_image c hcfix,hrtail]
          have hnewcontact : ∀ w, w ∈ (Chain.cons k r).support → w ∈ C.map '' S →
              w = b ∨ w = z := by
            intro w hw hS
            obtain ⟨x,hx,hxw⟩ := (show w ∈ C.map '' (Chain.cons k r).support by rw [htail]; exact hw)
            obtain ⟨y,hy,hyw⟩ := hS
            rcases (C.fibers x y).mp (hxw.trans hyw.symm) with hxy | ⟨hxf,_⟩
            · have hxS : x ∈ S := hxy ▸ hy
              rcases hcontact x (by rw [support_cons]; exact Or.inr hx) hxS with hxa | hxz
              · exact Or.inl (hxw.symm.trans ((congrArg C.map hxa).trans C.source))
              · exact Or.inr (hxw.symm.trans ((congrArg C.map hxz).trans hzfix))
            · exact Or.inl (hxw.symm.trans (hCF x hxf))
          obtain ⟨F,t,hFinj,hFb,hFz,htz,hFcontact⟩ := ih hq hbz (C.map '' S) hnewcontact
          refine ⟨F.comp C.map,t,?_,?_,?_,htz,?_⟩
          · intro x hx y hy heq
            apply hinj hx hy
            exact hFinj ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩ heq
          · change F (C.map a) = t
            rw [C.source,hFb]
          · change F (C.map z) = z
            rw [hzfix,hFz]
          · intro w hw hS
            apply hFcontact w hw
            obtain ⟨x,hx,hxw⟩ := hS
            exact ⟨C.map x,⟨x,hx,rfl⟩,hxw⟩

end PlanarHom.Polygonal.Chain
