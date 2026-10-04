import PlanarHom.RotationEvenSubgraphFaceCut
import PlanarHom.PlanarityLRContourPermutation
import PlanarHom.FinitePermutationCycleSigns

/-! NEW literal contour obtained by cutting precisely the boundary occurrences.
The derived face color is invariant under this contour. At a boundary host,
every selected corner reaches a selected boundary dart without any embedding
or interval certificate. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {A : Finset E} {root : Dart E}
variable (C : R.FaceCut A root)

def cutContour (_C : R.FaceCut A root) : Equiv.Perm (Dart E) := contourPermutation R (fun e=>decide (e∈A))

@[simp] theorem cutContour_boundary (a : Dart E) (ha : a.1∈A) :
    C.cutContour a=R.facePerm a := by
  exact contourPermutation_selected R _ a (decide_eq_true ha)

@[simp] theorem cutContour_nonboundary (a : Dart E) (ha : a.1∉A) :
    C.cutContour a=R.rotation a := by
  exact contourPermutation_port R _ a (decide_eq_false ha)

@[simp] theorem side_cutContour (a : Dart E) : C.side (C.cutContour a)=C.side a := by
  by_cases ha : a.1∈A
  · rw [C.cutContour_boundary a ha,C.side_facePerm]
  · rw [C.cutContour_nonboundary a ha,C.side_rotation_of_notMem a ha]

def selectedContour : Equiv.Perm {a : Dart E // C.side a=true} :=
  C.cutContour.subtypePerm (fun a=>by rw [C.side_cutContour])

theorem side_eq_of_sameCycle {a b : Dart E} (h : C.cutContour.SameCycle a b) :
    C.side a=C.side b := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hs : ∀n,C.side (C.cutContour^[n] a)=C.side a := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',C.side_cutContour,ih]
  simpa only [Equiv.Perm.iterate_eq_pow,hn] using (hs n).symm

/-- Stop at the first boundary dart encountered in a literal row traversal.
Only the existence of a boundary dart at the host is used. -/
theorem exists_boundary_sameCycle (a b : Dart E)
    (hb : b.1∈A) (hh : (G.dartPair a).1=(G.dartPair b).1) :
    ∃d : Dart E,d.1∈A ∧ (G.dartPair d).1=(G.dartPair a).1 ∧ C.cutContour.SameCycle a d := by
  obtain ⟨n,hn⟩ := R.exists_rotation_iterate_of_sameHost a b hh
  suffices h : ∀n (a : Dart E),R.rotation^[n] a=b →
      ∃d : Dart E,d.1∈A ∧ (G.dartPair d).1=(G.dartPair a).1 ∧ C.cutContour.SameCycle a d from h n a hn
  intro n
  induction n with
  | zero =>
      intro a ha
      have hab : a=b := ha
      exact ⟨a,hab ▸ hb,rfl,.rfl⟩
  | succ n ih =>
      intro a ha
      by_cases he : a.1∈A
      · exact ⟨a,he,rfl,.rfl⟩
      · have hn : R.rotation^[n] (R.rotation a)=b := by
          simpa only [Function.iterate_succ_apply] using ha
        obtain ⟨d,hd,hh,hs⟩ := ih (R.rotation a) hn
        refine ⟨d,hd,hh.trans (R.rotation_host a),?_⟩
        have hstep : C.cutContour.SameCycle a (R.rotation a) := by
          rw [←C.cutContour_nonboundary a he]
          exact Equiv.Perm.SameCycle.rfl.apply_right
        exact hstep.trans hs

/-- At a host with no boundary occurrence the cut contour is exactly its
original cyclic row, including a singleton row. -/
theorem sameCycle_of_no_boundary {v : V}
    (hv : ∀a : Dart E,(G.dartPair a).1=v → a.1∉A)
    (a b : Dart E) (ha : (G.dartPair a).1=v) (hb : (G.dartPair b).1=v) :
    C.cutContour.SameCycle a b := by
  obtain ⟨n,hn⟩ := R.exists_rotation_iterate_of_sameHost a b (ha.trans hb.symm)
  have hi : ∀n,C.cutContour.SameCycle a (R.rotation^[n] a) := by
    intro n
    induction n with
    | zero => exact .rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have he := hv (R.rotation^[n] a) (by rw [R.rotation_iterate_host,ha])
        rw [←C.cutContour_nonboundary _ he]
        exact ih.apply_right
  exact hn ▸ hi n

/-- A crossed dart connects to the other boundary dart at its target host.
Its own reverse has the opposite derived color and therefore cannot be the
first boundary reached by the color-preserving cut contour. -/
theorem boundary_step_to_other (a b : Dart E) (ha : a.1∈A) (hb : b.1∈A)
    (hhost : (G.dartPair b).1=(G.dartPair (reversePerm E a)).1)
    (honly : ∀d : Dart E,d.1∈A → (G.dartPair d).1=(G.dartPair b).1 →
      d=reversePerm E a ∨ d=b) : C.cutContour.SameCycle a b := by
  have hf : (G.dartPair (C.cutContour a)).1=(G.dartPair b).1 := by
    rw [C.cutContour_boundary a ha,R.facePerm_host,hhost]
  obtain ⟨d,hd,hh,hs⟩ := C.exists_boundary_sameCycle (C.cutContour a) b hb hf
  have had : C.cutContour.SameCycle a d := Equiv.Perm.SameCycle.rfl.apply_right.trans hs
  rcases honly d hd (hh.trans hf) with he|he
  · have hc := C.crosses_dart a
    have heq := C.side_eq_of_sameCycle had
    rw [he] at heq
    rw [←heq,decide_eq_true ha] at hc
    simp at hc
  · exact he ▸ had

theorem iterate_host_of_no_boundary {v : V}
    (hv : ∀a : Dart E,(G.dartPair a).1=v → a.1∉A)
    (a : Dart E) (ha : (G.dartPair a).1=v) (n : ℕ) :
    (G.dartPair (C.cutContour^[n] a)).1=v := by
  induction n with
  | zero => exact ha
  | succ n ih =>
      rw [Function.iterate_succ_apply',C.cutContour_nonboundary _ (hv _ ih),R.rotation_host,ih]

theorem sameCycle_host_of_no_boundary {v : V}
    (hv : ∀a : Dart E,(G.dartPair a).1=v → a.1∉A)
    (a b : Dart E) (ha : (G.dartPair a).1=v) (h : C.cutContour.SameCycle a b) :
    (G.dartPair b).1=v := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hi := C.iterate_host_of_no_boundary hv a ha n
  simpa only [Equiv.Perm.iterate_eq_pow,hn] using hi

theorem inside_of_selected_no_boundary {v : V}
    (hv : ∀a : Dart E,(G.dartPair a).1=v → a.1∉A)
    (a : Dart E) (ha : (G.dartPair a).1=v) (hs : C.side a=true) : C.InsideVertex v := by
  intro b hb
  exact (C.vertex_constant hv b a hb ha).trans hs

end PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
