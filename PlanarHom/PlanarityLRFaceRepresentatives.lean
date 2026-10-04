import PlanarHom.PlanarityLRFaceBoundary

/-! NEW canonical representatives of the exact computed permutation cycles. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityFaceCode

private theorem self_mem_filter (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    eraseDart a ∈ (PlanarityRotationCode.allDarts g).filter
      (fun b => decide (b ∈ orbit g bits (eraseDart a))) := by
  rw [List.mem_filter,decide_eq_true_eq,PlanarityRotationCode.mem_allDarts]
  exact ⟨a.1.isLt,(mem_orbit_iff_sameCycle g hg bits a a).mpr .rfl⟩

theorem representative_mem_orbit (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    representative g bits (eraseDart a) ∈ orbit g bits (eraseDart a) := by
  have hm := self_mem_filter g hg bits a
  unfold representative
  cases he : (PlanarityRotationCode.allDarts g).filter
      (fun b => decide (b ∈ orbit g bits (eraseDart a))) with
  | nil => rw [he] at hm; simp at hm
  | cons b bs =>
      have hb : b ∈ (PlanarityRotationCode.allDarts g).filter
          (fun b => decide (b ∈ orbit g bits (eraseDart a))) := by rw [he]; simp
      exact of_decide_eq_true (List.mem_filter.mp hb).2

theorem representative_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    (representative g bits (eraseDart a)).1 < g.edges.length :=
  orbit_index_valid g hg bits a (representative_mem_orbit g hg bits a)

theorem representative_eq_of_sameCycle (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a b : Dart (Fin g.edges.length))
    (hab : (facePermutation g hg bits).SameCycle a b) :
    representative g bits (eraseDart a) = representative g bits (eraseDart b) := by
  have hf : (PlanarityRotationCode.allDarts g).filter (fun c => decide (c ∈ orbit g bits (eraseDart a))) =
      (PlanarityRotationCode.allDarts g).filter (fun c => decide (c ∈ orbit g bits (eraseDart b))) := by
    apply List.filter_congr
    intro c hc
    have hv := (PlanarityRotationCode.mem_allDarts g c).mp hc
    have ha := mem_orbit_iff_sameCycle g hg bits a (liftDart c hv)
    have hb := mem_orbit_iff_sameCycle g hg bits b (liftDart c hv)
    simp only [erase_liftDart] at ha hb
    have hh : (c ∈ orbit g bits (eraseDart a)) ↔ (c ∈ orbit g bits (eraseDart b)) := by
      rw [ha,hb]
      exact ⟨fun h => hab.symm.trans h,fun h => hab.trans h⟩
    simp only [hh]
  have hm := self_mem_filter g hg bits a
  unfold representative
  rw [← hf]
  cases he : (PlanarityRotationCode.allDarts g).filter (fun c => decide (c ∈ orbit g bits (eraseDart a))) with
  | nil => rw [he] at hm; simp at hm
  | cons c cs => rfl

theorem representative_idempotent (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    representative g bits (representative g bits (eraseDart a)) = representative g bits (eraseDart a) := by
  let b := liftDart (representative g bits (eraseDart a)) (representative_valid g hg bits a)
  have hm := representative_mem_orbit g hg bits a
  have hc : (facePermutation g hg bits).SameCycle a b :=
    (mem_orbit_iff_sameCycle g hg bits a b).mp (by simpa only [b,erase_liftDart] using hm)
  simpa only [b,erase_liftDart] using (representative_eq_of_sameCycle g hg bits a b hc).symm

theorem representative_mem_representatives (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    representative g bits (eraseDart a) ∈ representatives g bits := by
  rw [representatives,List.mem_filter,decide_eq_true_eq,PlanarityRotationCode.mem_allDarts]
  exact ⟨representative_valid g hg bits a,representative_idempotent g hg bits a⟩

/-- Every valid dart belongs to the boundary of its actual table representative. -/
theorem mem_representative_boundary (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    eraseDart a ∈ boundary g bits (representative g bits (eraseDart a)) := by
  let b := liftDart (representative g bits (eraseDart a)) (representative_valid g hg bits a)
  have hc : (facePermutation g hg bits).SameCycle a b :=
    (mem_orbit_iff_sameCycle g hg bits a b).mp (by
      simpa only [b,erase_liftDart] using representative_mem_orbit g hg bits a)
  have hh := (mem_boundary_iff_orbit g hg bits b (eraseDart a)).mpr
    ((mem_orbit_iff_sameCycle g hg bits b a).mpr hc.symm)
  simpa only [b,erase_liftDart] using hh

 theorem representative_index_of_mem (g : MixedCode) (bits : List Bool)
    {a : PlanarityRotationCode.Dart} (ha : a ∈ representatives g bits) : a.1 < g.edges.length :=
  (PlanarityRotationCode.mem_allDarts g a).mp (List.mem_filter.mp ha).1

 theorem representative_fixed_of_mem (g : MixedCode) (bits : List Bool)
    {a : PlanarityRotationCode.Dart} (ha : a ∈ representatives g bits) : representative g bits a = a :=
  of_decide_eq_true (List.mem_filter.mp ha).2

/-- Distinct emitted representatives have genuinely disjoint dart boundaries. -/
theorem representative_boundaries_disjoint (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a b : PlanarityRotationCode.Dart}
    (ha : a ∈ representatives g bits) (hb : b ∈ representatives g bits) (hne : a ≠ b) :
    List.Disjoint (boundary g bits a) (boundary g bits b) := by
  rw [List.disjoint_left]
  intro c hca hcb
  let a' := liftDart a (representative_index_of_mem g bits ha)
  let b' := liftDart b (representative_index_of_mem g bits hb)
  have hca' : c ∈ orbit g bits (eraseDart a') :=
    (mem_boundary_iff_orbit g hg bits a' c).mp (by simpa only [a',erase_liftDart] using hca)
  have hcb' : c ∈ orbit g bits (eraseDart b') :=
    (mem_boundary_iff_orbit g hg bits b' c).mp (by simpa only [b',erase_liftDart] using hcb)
  let c' := liftDart c (orbit_index_valid g hg bits a' hca')
  have hac := (mem_orbit_iff_sameCycle g hg bits a' c').mp (by simpa only [c',erase_liftDart] using hca')
  have hbc := (mem_orbit_iff_sameCycle g hg bits b' c').mp (by simpa only [c',erase_liftDart] using hcb')
  have hh := representative_eq_of_sameCycle g hg bits a' b' (hac.trans hbc.symm)
  simp only [a',b',erase_liftDart,representative_fixed_of_mem g bits ha,
    representative_fixed_of_mem g bits hb] at hh
  exact hne hh

/-- The complete emitted face boundary list contains each literal occurrence dart
exactly once, including separate loop and parallel-edge darts. -/
theorem all_boundaries_nodup (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool) :
    ((representatives g bits).flatMap (boundary g bits)).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro a ha
    have hn := boundary_nodup g hg bits (liftDart a (representative_index_of_mem g bits ha))
    simpa only [erase_liftDart] using hn
  · apply (representatives_nodup g bits).imp_of_mem
    intro a b ha hb hne
    exact representative_boundaries_disjoint g hg bits ha hb hne

 theorem mem_all_boundaries (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (a : PlanarityRotationCode.Dart) :
    a ∈ (representatives g bits).flatMap (boundary g bits) ↔ a.1 < g.edges.length := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨b,hb,ha⟩
    let b' := liftDart b (representative_index_of_mem g bits hb)
    have ho := (mem_boundary_iff_orbit g hg bits b' a).mp (by simpa only [b',erase_liftDart] using ha)
    exact orbit_index_valid g hg bits b' ho
  · intro ha
    let a' := liftDart a ha
    refine ⟨representative g bits a,?_,?_⟩
    · simpa only [a',erase_liftDart] using representative_mem_representatives g hg bits a'
    · simpa only [a',erase_liftDart] using mem_representative_boundary g hg bits a'

 theorem all_boundaries_perm_allDarts (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool) :
    ((representatives g bits).flatMap (boundary g bits)).Perm (PlanarityRotationCode.allDarts g) := by
  apply (List.perm_ext_iff_of_nodup (all_boundaries_nodup g hg bits) (PlanarityRotationCode.allDarts_nodup g)).mpr
  intro a
  rw [mem_all_boundaries g hg bits a,PlanarityRotationCode.mem_allDarts]

end PlanarHom.PlanarityLRRealization
