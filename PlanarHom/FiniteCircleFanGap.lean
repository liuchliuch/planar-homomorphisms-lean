import PlanarHom.OccurrenceKasteleynCirclePortOrder

/-! NEW actual gap outside finitely many disjoint closed circle fans. This
constructs the missing circle chart cut from the continuous extended fans. -/
noncomputable section
open Set Topology
namespace PlanarHom.FiniteCircleFanGap
open MultiGraph RadialPottsAssemblyGeometry

/-- A finite family of disjoint embedded fan intervals has an actual common
omitted circle point. Each fan extends injectively to real transverse parameters,
so a small negative parameter lies beyond its initial endpoint and away from all
other compact fans. The omitted point is constructed, not assumed. -/
theorem exists_gap {ι : Type*} [Finite ι] (f : ι → C(ℝ,Plane))
    (hinj : ∀ i, Function.Injective (f i)) (hcircle : ∀ i t, rayLength (f i t)=1)
    (hdis : ∀ i j, i≠j → Disjoint (f i '' Set.Icc 0 1) (f j '' Set.Icc 0 1)) :
    ∃ p : Plane, rayLength p=1 ∧ ∀ i, p∉f i '' Set.Icc 0 1 := by
  classical
  rcases isEmpty_or_nonempty ι with hi | hi
  · letI := hi
    refine ⟨(0,1),?_,fun i => isEmptyElim i⟩
    norm_num [rayLength]
  · letI := hi
    let i : ι := Classical.choice hi
    let K : Set Plane := ⋃ j∈{j : ι | j≠i}, f j '' Set.Icc 0 1
    have hK : IsCompact K :=
      (Set.toFinite _).isCompact_biUnion (fun j _ => isCompact_Icc.image (f j).continuous)
    have h0 : f i 0 ∉ K := by
      intro hx
      simp only [K,Set.mem_iUnion,Set.mem_setOf_eq] at hx
      obtain ⟨j,hj,hx⟩ := hx
      exact Set.disjoint_left.mp (hdis i j hj.symm) ⟨0,by norm_num,rfl⟩ hx
    have hopen : IsOpen ((f i) ⁻¹' Kᶜ) := hK.isClosed.isOpen_compl.preimage (f i).continuous
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
    have ht : (-ε/2:ℝ)∈Metric.ball 0 ε := by
      rw [Metric.mem_ball,Real.dist_eq]
      simp only [sub_zero]
      rw [abs_of_neg (by linarith : -ε/2<0)]
      linarith
    have hpK : f i (-ε/2)∉K := hball ht
    refine ⟨f i (-ε/2),hcircle i _,?_⟩
    intro j hj
    by_cases heq : j=i
    · subst j
      obtain ⟨t,ht,he⟩ := hj
      have hh := hinj i he
      linarith [ht.1]
    · exact hpK (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨heq,hj⟩⟩)

end PlanarHom.FiniteCircleFanGap
