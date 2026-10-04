import PlanarHom.HostRowMarkerErasure

/-! Literal assembly of arbitrary complete local row systems under vertex
identification. Every dart retains its patch tag; only its host is identified. -/
noncomputable section
open Classical
namespace PlanarHom.HostRowSystem
variable {C V : Type} {W D : C → Type}
variable (F : ∀c,HostRowSystem (W c) (D c)) (place : ∀c,W c→V)
variable (vertices : ∀c,List (W c))
variable (hv : ∀c,(vertices c).Nodup) (hcover : ∀c w,w∈vertices c)

def localWord (c : C) (v : V) : List (D c) :=
  (vertices c).flatMap (fun w=>if place c w=v then (F c).row w else [])

include hcover in
theorem localWord_mem (c : C) (v : V) (a : D c) :
    a∈localWord F place vertices c v ↔ place c ((F c).host a)=v := by
  simp only [localWord,List.mem_flatMap]
  constructor
  · rintro ⟨w,_,ha⟩
    split_ifs at ha with hw
    · rw [((F c).mem w a).mp ha]
      exact hw
    · simp at ha
  · intro ha
    refine ⟨(F c).host a,hcover c _,?_⟩
    simp only [ha,if_pos]
    exact ((F c).mem _ a).mpr rfl

include hv in
theorem localWord_nodup (c : C) (v : V) : (localWord F place vertices c v).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro w _
    split_ifs
    · exact (F c).nodup w
    · exact List.nodup_nil
  · apply (hv c).imp
    intro w z hn
    apply List.disjoint_left.mpr
    intro a ha hb
    dsimp only at ha hb
    split_ifs at ha hb with hw hz
    · exact hn ((((F c).mem w a).mp ha).symm.trans (((F c).mem z a).mp hb))
    all_goals simp_all

def word (order : List C) (v : V) : List (Sigma D) :=
  order.flatMap (fun c=>(localWord F place vertices c v).map (Sigma.mk c))

include hv in
theorem word_nodup (order : List C) (ho : order.Nodup) (v : V) : (word F place vertices order v).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro c _
    exact (localWord_nodup F place vertices hv c v).map (by intro a b h; exact eq_of_heq (Sigma.mk.inj h).2)
  · apply ho.imp
    intro c d hn
    apply List.disjoint_left.mpr
    intro a ha hb
    obtain ⟨x,_,hx⟩:=List.mem_map.mp ha
    obtain ⟨y,_,hy⟩:=List.mem_map.mp hb
    exact hn (congrArg Sigma.fst (hx.trans hy.symm))

include hcover in
theorem word_mem (order : List C) (horder : ∀c,c∈order) (v : V) (a : Sigma D) :
    a∈word F place vertices order v ↔ place a.1 ((F a.1).host a.2)=v := by
  simp only [word,List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨c,_,b,hb,rfl⟩
    exact (localWord_mem F place vertices hcover c v b).mp hb
  · obtain ⟨c,a⟩:=a
    intro ha
    exact ⟨c,horder c,a,(localWord_mem F place vertices hcover c v a).mpr ha,rfl⟩

def assemble (order : List C) (ho : order.Nodup) (horder : ∀c,c∈order) : HostRowSystem V (Sigma D) where
  host a := place a.1 ((F a.1).host a.2)
  row := word F place vertices order
  nodup := word_nodup F place vertices hv order ho
  mem := word_mem F place vertices hcover order horder

end PlanarHom.HostRowSystem
