import PlanarHom.PlanarityDepthFirstSearchTermination

/-! NEW reconstruction. The pending enter/exit program is correctly bracketed,
and its live vertices form the literal chain stored in discovery records. -/
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity

inductive WorkPaths : List ℕ → List Task → Prop
  | nil : WorkPaths [] []
  | enter (active : List ℕ) (t : Task) (rest : List Task)
      (ht : t.enter=true) (hp : t.path=active) (hr : WorkPaths active rest) :
      WorkPaths active (t::rest)
  | exit (active : List ℕ) (t : Task) (rest : List Task)
      (ht : t.enter=false) (hr : WorkPaths active rest) :
      WorkPaths (t.vertex::active) (t::rest)

 theorem WorkPaths.enter_prefix {active : List ℕ} {tail : List Task} (h : WorkPaths active tail)
    (tasks : List Task) (ht : ∀t∈tasks,t.enter=true ∧ t.path=active) :
    WorkPaths active (tasks++tail) := by
  induction tasks with
  | nil => exact h
  | cons t tasks ih =>
    exact .enter active t _ (ht t List.mem_cons_self).1 (ht t List.mem_cons_self).2
      (ih (fun a ha=>ht a (List.mem_cons_of_mem _ ha)))

 theorem workPaths_initial (g : MixedCode) : WorkPaths (initial g).active (initial g).work := by
  have hh := WorkPaths.enter_prefix WorkPaths.nil
    ((List.range g.vertices).map (fun v => enterTask v g.edges.length []))
    (by intro t ht; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht; exact ⟨rfl,rfl⟩)
  simpa [initial] using hh

 theorem WorkPaths.enter_tail {active : List ℕ} {t : Task} {rest : List Task}
    (h : WorkPaths active (t::rest)) (ht : t.enter=true) :
    t.path=active ∧ WorkPaths active rest := by
  cases h with
  | enter active t rest henter hp hr => exact ⟨hp,hr⟩
  | exit active t rest henter hr => simp [henter] at ht

 theorem WorkPaths.exit_tail {active : List ℕ} {t : Task} {rest : List Task}
    (h : WorkPaths active (t::rest)) (ht : t.enter=false) :
    ∃ tail, active=t.vertex::tail ∧ WorkPaths tail rest := by
  cases h with
  | enter active t rest henter hp hr => simp [henter] at ht
  | exit active t rest henter hr => exact ⟨active,rfl,hr⟩

 theorem workPaths_step (g : MixedCode) (s : State) (h : WorkPaths s.active s.work) :
    WorkPaths (step g s).active (step g s).work := by
  cases hw : s.work with
  | nil => simpa [step,hw] using h
  | cons t rest =>
    rw [hw] at h
    cases ht : t.enter with
    | true =>
      obtain ⟨hpath,hr⟩ := h.enter_tail ht
      simp only [step,hw,ht,↓reduceIte]
      split_ifs
      · exact WorkPaths.enter_prefix (WorkPaths.exit s.active (exitTask t.vertex) rest rfl hr)
          (childTasks g t.vertex (t.vertex::s.active))
          (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact ⟨rfl,rfl⟩)
      · exact hr
    | false =>
      obtain ⟨active,he,hr⟩ := h.exit_tail ht
      simpa [step,hw,ht,he] using hr

/-- Each chain link is an immutable actual discovery record. -/
inductive Chain (records : List Discovery) : List ℕ → Prop
  | nil : Chain records []
  | cons (r : Discovery) (hr : r∈records) (hpath : Chain records r.ancestors) :
      Chain records (r.vertex::r.ancestors)

 theorem Chain.mono {rs ss : List Discovery} (hsub : ∀r∈rs,r∈ss) {path : List ℕ}
    (h : Chain rs path) : Chain ss path := by
  induction h with
  | nil => exact .nil
  | cons r hr hc ih => exact .cons r (hsub r hr) ih

 theorem Chain.tail {rs : List Discovery} {path : List ℕ} (h : Chain rs path) : Chain rs path.tail := by
  cases h with
  | nil => exact .nil
  | cons r hr hp => exact hp

structure StackInvariant (g : MixedCode) (s : State) : Prop where
  goodSeen : GoodSeen g s
  paths : WorkPaths s.active s.work
  active_nodup : s.active.Nodup
  active_seen : ∀v∈s.active,v∈seen s
  finished_seen : ∀v∈s.finished,v∈seen s
  seen_split : ∀v∈seen s,v∈s.active ∨ v∈s.finished
  disjoint : List.Disjoint s.active s.finished
  active_chain : Chain s.discovered s.active
  record_chains : ∀r∈s.discovered,Chain s.discovered r.ancestors

 theorem stackInvariant_initial (g : MixedCode) : StackInvariant g (initial g) := by
  refine ⟨goodSeen_initial g,workPaths_initial g,by simp [initial],?_,?_,?_,?_,.nil,?_⟩
  all_goals simp [initial,seen]

 theorem stackInvariant_step (g : MixedCode) (s : State) (h : StackInvariant g s) :
    StackInvariant g (step g s) := by
  have hg := goodSeen_step g s h.goodSeen
  have hp := workPaths_step g s h.paths
  cases hw : s.work with
  | nil => simpa [step,hw] using h
  | cons t rest =>
    have paths := h.paths
    rw [hw] at paths
    cases ht : t.enter with
    | true =>
      obtain ⟨hpath,hrest⟩ := paths.enter_tail ht
      by_cases hnew : t.vertex<g.vertices ∧ t.vertex∉seen s
      · have hva : t.vertex∉s.active := fun hm=>hnew.2 (h.active_seen _ hm)
        have hvf : t.vertex∉s.finished := fun hm=>hnew.2 (h.finished_seen _ hm)
        have hm : ∀r∈s.discovered,r∈(⟨t.vertex,t.edge,s.active⟩:Discovery)::s.discovered :=
          fun r hr=>List.mem_cons_of_mem _ hr
        simp only [step,hw,ht,hnew,↓reduceIte] at hg hp ⊢
        refine ⟨hg,hp,List.nodup_cons.mpr ⟨hva,h.active_nodup⟩,?_,?_,?_,?_,?_,?_⟩
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · simp [seen]
          · exact List.mem_cons_of_mem _ (h.active_seen v hv)
        · intro v hv
          exact List.mem_cons_of_mem _ (h.finished_seen v hv)
        · intro v hv
          change v∈t.vertex::seen s at hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact Or.inl List.mem_cons_self
          · rcases h.seen_split v hv with hv | hv
            · exact Or.inl (List.mem_cons_of_mem _ hv)
            · exact Or.inr hv
        · exact List.disjoint_cons_left.mpr ⟨hvf,h.disjoint⟩
        · exact .cons ⟨t.vertex,t.edge,s.active⟩ List.mem_cons_self (h.active_chain.mono hm)
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact h.active_chain.mono hm
          · exact (h.record_chains r hr).mono hm
      · simpa [step,hw,ht,hnew] using
          (show StackInvariant g ⟨rest,s.active,s.discovered,s.finished⟩ from
            ⟨h.goodSeen,hrest,h.active_nodup,h.active_seen,h.finished_seen,h.seen_split,
              h.disjoint,h.active_chain,h.record_chains⟩)
    | false =>
      obtain ⟨active,he,hrest⟩ := paths.exit_tail ht
      simp only [step,hw,ht,↓reduceIte] at hg hp ⊢
      refine ⟨hg,hp,h.active_nodup.tail,?_,?_,?_,?_,h.active_chain.tail,h.record_chains⟩
      · intro v hv
        exact h.active_seen v (List.mem_of_mem_tail hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.active_seen _ (by simp [he])
        · exact h.finished_seen v hv
      · intro v hv
        rcases h.seen_split v hv with hv | hv
        · rw [he] at hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact Or.inr List.mem_cons_self
          · exact Or.inl (by simpa [he] using hv)
        · exact Or.inr (List.mem_cons_of_mem _ hv)
      · apply List.disjoint_cons_right.mpr
        constructor
        · have hn := h.active_nodup
          rw [he] at hn
          simpa [he] using hn.notMem
        · intro v hv hf
          exact h.disjoint (List.mem_of_mem_tail hv) hf

 theorem stackInvariant_iterate (g : MixedCode) (n : ℕ) :
    StackInvariant g ((step g)^[n] (initial g)) := by
  induction n with
  | zero => exact stackInvariant_initial g
  | succ n ih => rw [Function.iterate_succ_apply']; exact stackInvariant_step g _ ih

end PlanarHom.PlanarityDepthFirstSearch
