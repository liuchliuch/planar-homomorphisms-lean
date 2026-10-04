import PlanarHom.CircleBoundaryArcs

/-! NEW exact range descriptions of all circular corner arcs. In particular the
wrap corner covers exactly the two unbounded height rays and the omitted pole. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.CircleBoundaryArcs
open MultiGraph RadialPottsAssemblyGeometry PlanarityCircleCrossing

private def fractionParameter (d : ℝ) (hd : 0≤d) : I :=
  ⟨d/(d+1),⟨div_nonneg hd (by linarith),(div_le_one (by linarith : 0<d+1)).mpr (by linarith)⟩⟩

private theorem fractionParameter_ne_one (d : ℝ) (hd : 0≤d) : fractionParameter d hd≠1 := by
  intro h
  have hv := congrArg (fun t : I => (t:ℝ)) h
  change d/(d+1)=1 at hv
  have hh := (div_lt_one (by linarith : 0<d+1)).mpr (by linarith : d<d+1)
  linarith

private theorem fractionParameter_quotient (d : ℝ) (hd : 0≤d) :
    (fractionParameter d hd:ℝ)/(1-(fractionParameter d hd:ℝ))=d := by
  have hden : d+1≠0 := by linarith
  dsimp [fractionParameter]
  field_simp
  ring

/-- A tail's complete range, including its pole endpoint. -/
theorem northArc_range (a k : ℝ) (hk : k≠0) :
    Set.range (northArc a k hk) = {(0,1)} ∪
      (fun y : ℝ => diskMap (0,y)) '' {y | 0≤(y-a)/k} := by
  ext p
  constructor
  · rintro ⟨t,rfl⟩
    by_cases ht : t=1
    · left
      exact (northArc_eq_pole_iff a k hk t).mpr ht
    · right
      refine ⟨a+k*((t:ℝ)/(1-(t:ℝ))),?_,(northArc_finite a k hk ht).symm⟩
      have hnonneg : 0≤(t:ℝ)/(1-(t:ℝ)) := div_nonneg t.property.1 (by linarith [t.property.2])
      have he : (a+k*((t:ℝ)/(1-(t:ℝ)))-a)/k=(t:ℝ)/(1-(t:ℝ)) := by field_simp; ring
      change 0≤(a+k*((t:ℝ)/(1-(t:ℝ)))-a)/k
      rw [he]
      exact hnonneg
  · rintro (hp | ⟨y,hy,rfl⟩)
    · exact ⟨1,(northArc_one a k hk).trans hp.symm⟩
    · let t := fractionParameter ((y-a)/k) hy
      refine ⟨t,?_⟩
      rw [northArc_finite a k hk (fractionParameter_ne_one _ hy),fractionParameter_quotient]
      have he : a+k*((y-a)/k)=y := by field_simp; ring
      rw [he]

theorem northArc_range_positive (a : ℝ) :
    Set.range (northArc a 1 (by norm_num)) = {(0,1)} ∪
      (fun y : ℝ => diskMap (0,y)) '' Set.Ici a := by
  rw [northArc_range]
  congr 2
  ext y
  simp

theorem northArc_range_negative (a : ℝ) :
    Set.range (northArc a (-1) (by norm_num)) = {(0,1)} ∪
      (fun y : ℝ => diskMap (0,y)) '' Set.Iic a := by
  rw [northArc_range]
  congr 2
  ext y
  simp only [Set.mem_setOf_eq,Set.mem_Iic,div_neg,div_one,neg_nonneg,sub_nonpos]

/-- The omitted pole is included, and only heights outside the finite middle
interval occur. This is the literal last-to-first row corner. -/
theorem wrappingArc_range (a b : ℝ) :
    Set.range (wrappingArc a b) = {(0,1)} ∪
      (fun y : ℝ => diskMap (0,y)) '' (Set.Ici a ∪ Set.Iic b) := by
  change Set.range ((northPath a 1 (by norm_num)).trans (northPath b (-1) (by norm_num)).symm)=_
  rw [Path.trans_range,Path.symm_range]
  change Set.range (northArc a 1 (by norm_num)) ∪ Set.range (northArc b (-1) (by norm_num))=_
  rw [northArc_range_positive,northArc_range_negative,Set.image_union]
  ext p
  simp only [Set.mem_union]
  tauto

/-- The finite corner covers its entire closed height interval exactly. -/
theorem finiteArc_range {a b : ℝ} (hab : a≤b) :
    Set.range (finiteArc a b) = (fun y : ℝ => diskMap (0,y)) '' Set.Icc a b := by
  change Set.range ((fun y : ℝ => diskMap (0,y)) ∘ (Path.segment a b))=_
  rw [Set.range_comp,Path.range_segment,segment_eq_Icc hab]

/-- A wrapping corner avoids every strictly intervening finite-height port. -/
theorem wrappingArc_avoids_middle {a b y : ℝ} (hby : b<y) (hya : y<a) :
    diskMap (0,y)∉Set.range (wrappingArc a b) := by
  rw [wrappingArc_range]
  rintro (hp | ⟨z,(hz | hz),he⟩)
  · exact diskMap_boundary_ne_pole y hp
  · have hh := diskMap_boundary_injective he
    exact not_le_of_gt hya (hh ▸ hz)
  · have hh := diskMap_boundary_injective he
    exact not_le_of_gt hby (hh ▸ hz)

end PlanarHom.CircleBoundaryArcs
