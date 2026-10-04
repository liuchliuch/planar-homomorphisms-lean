import PlanarHom.PlanarityDepthFirstSearchStack

/-! NEW reconstruction. Every pending close is preceded by visits covering its
undiscovered valid neighbours. Consequently a finished vertex has no unseen
valid neighbour; this is the critical depth-first, rather than breadth-first,
property used to rule out cross edges. -/
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity

def Closed (g : MixedCode) (visited : List ℕ) (v : ℕ) : Prop :=
  ∀a∈neighbours g v,a.1<g.vertices → a.1∈visited

def Covered (g : MixedCode) (visited : List ℕ) : List Task → Prop
  | [] => True
  | t::rest => if t.enter then Covered g (t.vertex::visited) rest
      else Closed g visited t.vertex ∧ Covered g visited rest

 theorem Closed.mono {g : MixedCode} {xs ys : List ℕ} (hsub : ∀v∈xs,v<g.vertices→v∈ys)
    {v : ℕ} (h : Closed g xs v) : Closed g ys v := by
  intro a ha hv
  exact hsub a.1 (h a ha hv) hv

 theorem Covered.mono {g : MixedCode} {xs ys : List ℕ} (hsub : ∀v∈xs,v<g.vertices→v∈ys)
    {work : List Task} (h : Covered g xs work) : Covered g ys work := by
  induction work generalizing xs ys with
  | nil => trivial
  | cons t rest ih =>
    cases ht : t.enter with
    | false =>
      simp only [Covered,ht,Bool.false_eq_true,↓reduceIte] at h ⊢
      exact ⟨h.1.mono hsub,ih hsub h.2⟩
    | true =>
      simp only [Covered,ht,↓reduceIte] at h ⊢
      apply ih (fun v hv hvalid => ?_) h
      rcases List.mem_cons.mp hv with rfl | hv
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub v hv hvalid)

 theorem Covered.prepend_enters {g : MixedCode} (tasks : List Task) (rest : List Task)
    (visited : List ℕ) (ht : ∀t∈tasks,t.enter=true)
    (h : Covered g ((tasks.map Task.vertex).reverse++visited) rest) :
    Covered g visited (tasks++rest) := by
  induction tasks generalizing visited with
  | nil => simpa using h
  | cons t tasks ih =>
    simp only [List.cons_append,Covered,ht t List.mem_cons_self,↓reduceIte]
    apply ih (t.vertex::visited) (fun a ha=>ht a (List.mem_cons_of_mem _ ha))
    simpa [List.reverse_cons,List.append_assoc] using h

 theorem Covered.visit_block {g : MixedCode} {visited : List ℕ} {rest : List Task}
    (v : ℕ) (active : List ℕ) (h : Covered g visited rest) :
    Covered g visited (childTasks g v active ++ exitTask v :: rest) := by
  apply Covered.prepend_enters
  · intro t ht
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    rfl
  · simp only [Covered,exitTask,Bool.false_eq_true,↓reduceIte]
    constructor
    · intro a ha hv
      apply List.mem_append_left
      apply List.mem_reverse.mpr
      exact List.mem_map.mpr ⟨enterTask a.1 a.2 active,List.mem_map.mpr ⟨a,ha,rfl⟩,rfl⟩
    · exact h.mono (fun u hu hv => List.mem_append_right _ hu)

structure CoverageInvariant (g : MixedCode) (s : State) : Prop where
  pending : Covered g (seen s) s.work
  finished : ∀v∈s.finished,Closed g (seen s) v
  roots : ∀v, v<g.vertices → v∈seen s ∨ ∃t∈s.work,t.enter=true ∧ t.vertex=v

 theorem coverageInvariant_initial (g : MixedCode) : CoverageInvariant g (initial g) := by
  constructor
  · have hh := Covered.prepend_enters (g:=g)
      ((List.range g.vertices).map (fun v => enterTask v g.edges.length [])) [] []
      (by intro t ht; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht; rfl) (by trivial)
    simpa [initial,seen] using hh
  · simp [initial]
  · intro v hv
    right
    exact ⟨enterTask v g.edges.length [],List.mem_map.mpr ⟨v,List.mem_range.mpr hv,rfl⟩,rfl,rfl⟩

 theorem coverageInvariant_step (g : MixedCode) (s : State) (h : CoverageInvariant g s) :
    CoverageInvariant g (step g s) := by
  cases hw : s.work with
  | nil => simpa [step,hw] using h
  | cons t rest =>
    have hp := h.pending
    rw [hw] at hp
    have hmono := seen_step_mono g s
    cases ht : t.enter with
    | true =>
      simp only [Covered,ht,↓reduceIte] at hp
      by_cases hn : t.vertex<g.vertices ∧ t.vertex∉seen s
      · simp only [step,hw,ht,hn,↓reduceIte]
        refine ⟨?_,?_,?_⟩
        · exact Covered.visit_block t.vertex _ hp
        · intro v hv
          exact (h.finished v hv).mono (fun u hu _=>List.mem_cons_of_mem _ hu)
        · intro v hv
          rcases h.roots v hv with hs | ⟨a,ha,hat,hav⟩
          · exact Or.inl (List.mem_cons_of_mem _ hs)
          · rw [hw] at ha
            rcases List.mem_cons.mp ha with rfl | ha
            · left; simp [seen,hav]
            · right
              exact ⟨a,List.mem_append_right _ (List.mem_cons_of_mem _ ha),hat,hav⟩
      · have hsub : ∀v∈t.vertex::seen s,v<g.vertices→v∈seen s := by
          intro v hv hvn
          rcases List.mem_cons.mp hv with rfl | hv
          · by_contra hv
            exact hn ⟨hvn,hv⟩
          · exact hv
        simp only [step,hw,ht,hn,↓reduceIte]
        refine ⟨hp.mono hsub,h.finished,?_⟩
        intro v hv
        rcases h.roots v hv with hs | ⟨a,ha,hat,hav⟩
        · exact Or.inl hs
        · rw [hw] at ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact Or.inl (hsub v (by simp [hav]) hv)
          · exact Or.inr ⟨a,ha,hat,hav⟩
    | false =>
      simp only [Covered,ht,Bool.false_eq_true,↓reduceIte] at hp
      simp only [step,hw,ht,Bool.false_eq_true,↓reduceIte]
      refine ⟨hp.2,?_,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hp.1
        · exact h.finished v hv
      · intro v hv
        rcases h.roots v hv with hs | ⟨a,ha,hat,hav⟩
        · exact Or.inl hs
        · rw [hw] at ha
          rcases List.mem_cons.mp ha with rfl | ha
          · simp [ht] at hat
          · exact Or.inr ⟨a,ha,hat,hav⟩

 theorem coverageInvariant_iterate (g : MixedCode) (n : ℕ) :
    CoverageInvariant g ((step g)^[n] (initial g)) := by
  induction n with
  | zero => exact coverageInvariant_initial g
  | succ n ih => rw [Function.iterate_succ_apply']; exact coverageInvariant_step g _ ih

 theorem all_vertices_discovered (g : MixedCode) {v : ℕ} (hv : v<g.vertices) : v∈seen (run g) := by
  rcases (coverageInvariant_iterate g (fuel g)).roots v hv with h | ⟨t,ht,_,_⟩
  · exact h
  · change t∈(run g).work at ht
    rw [run_complete] at ht
    simp at ht

end PlanarHom.PlanarityDepthFirstSearch
