import PlanarHom.PlanarityRowFaceBoundary

/-! NEW canonical representatives of the exact computed permutation cycles. -/
noncomputable section
namespace PlanarHom.PlanarityRowFaceCode
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRealization

private theorem self_mem_filter (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) :
    eraseDart a ∈ (PlanarityRotationCode.allDarts g).filter
      (fun b => decide (b ∈ orbit g rows (eraseDart a))) := by
  rw [List.mem_filter,decide_eq_true_eq,PlanarityRotationCode.mem_allDarts]
  exact ⟨a.1.isLt,(mem_orbit_iff_sameCycle g hg rows R hrows a a).mpr .rfl⟩

theorem representative_mem_orbit (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) :
    representative g rows (eraseDart a) ∈ orbit g rows (eraseDart a) := by
  have hm := self_mem_filter g hg rows R hrows a
  unfold representative
  cases he : (PlanarityRotationCode.allDarts g).filter
      (fun b => decide (b ∈ orbit g rows (eraseDart a))) with
  | nil => rw [he] at hm; simp at hm
  | cons b bs =>
      have hb : b ∈ (PlanarityRotationCode.allDarts g).filter
          (fun b => decide (b ∈ orbit g rows (eraseDart a))) := by rw [he]; simp
      exact of_decide_eq_true (List.mem_filter.mp hb).2

theorem representative_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) :
    (representative g rows (eraseDart a)).1 < g.edges.length :=
  orbit_index_valid g hg rows R hrows a (representative_mem_orbit g hg rows R hrows a)

theorem representative_eq_of_sameCycle (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a b : Dart (Fin g.edges.length))
    (hab : (R.facePerm).SameCycle a b) :
    representative g rows (eraseDart a) = representative g rows (eraseDart b) := by
  have hf : (PlanarityRotationCode.allDarts g).filter (fun c => decide (c ∈ orbit g rows (eraseDart a))) =
      (PlanarityRotationCode.allDarts g).filter (fun c => decide (c ∈ orbit g rows (eraseDart b))) := by
    apply List.filter_congr
    intro c hc
    have hv := (PlanarityRotationCode.mem_allDarts g c).mp hc
    have ha := mem_orbit_iff_sameCycle g hg rows R hrows a (liftDart c hv)
    have hb := mem_orbit_iff_sameCycle g hg rows R hrows b (liftDart c hv)
    simp only [erase_liftDart] at ha hb
    have hh : (c ∈ orbit g rows (eraseDart a)) ↔ (c ∈ orbit g rows (eraseDart b)) := by
      rw [ha,hb]
      exact ⟨fun h => hab.symm.trans h,fun h => hab.trans h⟩
    simp only [hh]
  have hm := self_mem_filter g hg rows R hrows a
  unfold representative
  rw [← hf]
  cases he : (PlanarityRotationCode.allDarts g).filter (fun c => decide (c ∈ orbit g rows (eraseDart a))) with
  | nil => rw [he] at hm; simp at hm
  | cons c cs => rfl

theorem representative_idempotent (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) :
    representative g rows (representative g rows (eraseDart a)) = representative g rows (eraseDart a) := by
  let b := liftDart (representative g rows (eraseDart a)) (representative_valid g hg rows R hrows a)
  have hm := representative_mem_orbit g hg rows R hrows a
  have hc : (R.facePerm).SameCycle a b :=
    (mem_orbit_iff_sameCycle g hg rows R hrows a b).mp (by simpa only [b,erase_liftDart] using hm)
  simpa only [b,erase_liftDart] using (representative_eq_of_sameCycle g hg rows R hrows a b hc).symm

theorem representative_mem_representatives (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) :
    representative g rows (eraseDart a) ∈ representatives g rows := by
  rw [representatives,List.mem_filter,decide_eq_true_eq,PlanarityRotationCode.mem_allDarts]
  exact ⟨representative_valid g hg rows R hrows a,representative_idempotent g hg rows R hrows a⟩

/-- Every valid dart belongs to the boundary of its actual table representative. -/
theorem mem_representative_boundary (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) :
    eraseDart a ∈ boundary g rows (representative g rows (eraseDart a)) := by
  let b := liftDart (representative g rows (eraseDart a)) (representative_valid g hg rows R hrows a)
  have hc : (R.facePerm).SameCycle a b :=
    (mem_orbit_iff_sameCycle g hg rows R hrows a b).mp (by
      simpa only [b,erase_liftDart] using representative_mem_orbit g hg rows R hrows a)
  have hh := (mem_boundary_iff_orbit g hg rows R hrows b (eraseDart a)).mpr
    ((mem_orbit_iff_sameCycle g hg rows R hrows b a).mpr hc.symm)
  simpa only [b,erase_liftDart] using hh

 theorem representative_index_of_mem (g : MixedCode) (rows : Rows)
    {a : PlanarityRotationCode.Dart} (ha : a ∈ representatives g rows) : a.1 < g.edges.length :=
  (PlanarityRotationCode.mem_allDarts g a).mp (List.mem_filter.mp ha).1

 theorem representative_fixed_of_mem (g : MixedCode) (rows : Rows)
    {a : PlanarityRotationCode.Dart} (ha : a ∈ representatives g rows) : representative g rows a = a :=
  of_decide_eq_true (List.mem_filter.mp ha).2

/-- Distinct emitted representatives have genuinely disjoint dart boundaries. -/
theorem representative_boundaries_disjoint (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) {a b : PlanarityRotationCode.Dart}
    (ha : a ∈ representatives g rows) (hb : b ∈ representatives g rows) (hne : a ≠ b) :
    List.Disjoint (boundary g rows a) (boundary g rows b) := by
  rw [List.disjoint_left]
  intro c hca hcb
  let a' := liftDart a (representative_index_of_mem g rows ha)
  let b' := liftDart b (representative_index_of_mem g rows hb)
  have hca' : c ∈ orbit g rows (eraseDart a') :=
    (mem_boundary_iff_orbit g hg rows R hrows a' c).mp (by simpa only [a',erase_liftDart] using hca)
  have hcb' : c ∈ orbit g rows (eraseDart b') :=
    (mem_boundary_iff_orbit g hg rows R hrows b' c).mp (by simpa only [b',erase_liftDart] using hcb)
  let c' := liftDart c (orbit_index_valid g hg rows R hrows a' hca')
  have hac := (mem_orbit_iff_sameCycle g hg rows R hrows a' c').mp (by simpa only [c',erase_liftDart] using hca')
  have hbc := (mem_orbit_iff_sameCycle g hg rows R hrows b' c').mp (by simpa only [c',erase_liftDart] using hcb')
  have hh := representative_eq_of_sameCycle g hg rows R hrows a' b' (hac.trans hbc.symm)
  simp only [a',b',erase_liftDart,representative_fixed_of_mem g rows ha,
    representative_fixed_of_mem g rows hb] at hh
  exact hne hh

/-- The complete emitted face boundary list contains each literal occurrence dart
exactly once, including separate loop and parallel-edge darts. -/
theorem all_boundaries_nodup (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) :
    ((representatives g rows).flatMap (boundary g rows)).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro a ha
    have hn := boundary_nodup g hg rows R hrows (liftDart a (representative_index_of_mem g rows ha))
    simpa only [erase_liftDart] using hn
  · apply (representatives_nodup g rows).imp_of_mem
    intro a b ha hb hne
    exact representative_boundaries_disjoint g hg rows R hrows ha hb hne

 theorem mem_all_boundaries (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R)
    (a : PlanarityRotationCode.Dart) :
    a ∈ (representatives g rows).flatMap (boundary g rows) ↔ a.1 < g.edges.length := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨b,hb,ha⟩
    let b' := liftDart b (representative_index_of_mem g rows hb)
    have ho := (mem_boundary_iff_orbit g hg rows R hrows b' a).mp (by simpa only [b',erase_liftDart] using ha)
    exact orbit_index_valid g hg rows R hrows b' ho
  · intro ha
    let a' := liftDart a ha
    refine ⟨representative g rows a,?_,?_⟩
    · simpa only [a',erase_liftDart] using representative_mem_representatives g hg rows R hrows a'
    · simpa only [a',erase_liftDart] using mem_representative_boundary g hg rows R hrows a'

 theorem all_boundaries_perm_allDarts (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) :
    ((representatives g rows).flatMap (boundary g rows)).Perm (PlanarityRotationCode.allDarts g) := by
  apply (List.perm_ext_iff_of_nodup (all_boundaries_nodup g hg rows R hrows) (PlanarityRotationCode.allDarts_nodup g)).mpr
  intro a
  rw [mem_all_boundaries g hg rows R hrows a,PlanarityRotationCode.mem_allDarts]

end PlanarHom.PlanarityRowFaceCode
