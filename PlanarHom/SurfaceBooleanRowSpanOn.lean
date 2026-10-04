import PlanarHom.SurfaceBooleanFiniteQuotient

/-! NEW width-indexed span interface, avoiding incidental header-list casts
in graph incidence and supplied-face semantics. -/
namespace PlanarHom.SurfaceBooleanRows

def rowSpanOn (m : ℕ) (rs : List Row) : Submodule (ZMod 2) (Fin m→ZMod 2) :=
  Submodule.span (ZMod 2) {x | ∃r∈rs,finiteValue m r=x}

theorem rowSpanOn_eq_finiteSpan (shape : Row) (rs : List Row) :
    rowSpanOn shape.length rs=finiteSpan shape rs := by
  rw [finiteSpan_eq]
  congr 1
  ext x
  simp [List.mem_map,rowSpanOn]

theorem inputSpan_eq_extend_on (m : ℕ) (rs : List Row) (hw : ∀r∈rs,r.length≤m) :
    inputSpan rs=(rowSpanOn m rs).map (extendVector m) := by
  rw [inputSpan,rowSpanOn,Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    refine ⟨finiteValue m r,⟨r,hr,rfl⟩,?_⟩
    exact extend_restrict m (value r) (value_bounded m r (hw r hr))
  · rintro ⟨y,⟨r,hr,rfl⟩,hx⟩
    refine ⟨r,hr,?_⟩
    exact (extend_restrict m (value r) (value_bounded m r (hw r hr))).symm.trans hx

theorem extend_mem_inputSpan_on_iff (m : ℕ) (rs : List Row)
    (hw : ∀r∈rs,r.length≤m) (x : Fin m→ZMod 2) :
    extendVector m x∈inputSpan rs ↔ x∈rowSpanOn m rs := by
  rw [inputSpan_eq_extend_on m rs hw]
  constructor
  · rintro ⟨y,hy,he⟩
    exact (extend_injective m he) ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem inputSpan_bounded_on (m : ℕ) (rs : List Row)
    (hw : ∀r∈rs,r.length≤m) (x : Vector) (hx : x∈inputSpan rs) : Bounded m x := by
  rw [inputSpan_eq_extend_on m rs hw] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  intro i hi
  simp [show ¬i<m by omega]

def quotientEncodeOn (m : ℕ) (faces cycles : List Row) :
    (Fin m→ZMod 2) →ₗ[ZMod 2] (Fin (quotientRows faces cycles).length→ZMod 2) :=
  (quotientEncode faces cycles).comp (extendVector m)

def quotientLiftOn (m : ℕ) (faces cycles : List Row) :
    (Fin (quotientRows faces cycles).length→ZMod 2) →ₗ[ZMod 2] (Fin m→ZMod 2) :=
  (restrictVector m).comp (quotientLift faces cycles)

theorem quotientEncodeOn_lift (m : ℕ) (faces cycles : List Row)
    (hw : ∀r∈cycles,r.length≤m) (hsub : inputSpan faces ≤ inputSpan cycles)
    (x : Fin (quotientRows faces cycles).length→ZMod 2) :
    quotientEncodeOn m faces cycles (quotientLiftOn m faces cycles x)=x := by
  change quotientEncode faces cycles (extendVector m (restrictVector m (quotientLift faces cycles x)))=x
  rw [extend_restrict _ _ (inputSpan_bounded_on m cycles hw _ (quotientLift_mem faces cycles hsub x))]
  exact quotientEncode_lift faces cycles x

theorem quotientEncodeOn_kernel (m : ℕ) (faces cycles : List Row)
    (hf : ∀r∈faces,r.length≤m) (hc : ∀r∈cycles,r.length≤m)
    (x : Fin m→ZMod 2) (hx : x∈rowSpanOn m cycles) :
    quotientEncodeOn m faces cycles x=0 ↔ x∈rowSpanOn m faces := by
  change quotientEncode faces cycles (extendVector m x)=0 ↔ _
  rw [quotientEncode_kernel faces cycles _ ((extend_mem_inputSpan_on_iff m cycles hc x).mpr hx),
    extend_mem_inputSpan_on_iff m faces hf x]

end PlanarHom.SurfaceBooleanRows
