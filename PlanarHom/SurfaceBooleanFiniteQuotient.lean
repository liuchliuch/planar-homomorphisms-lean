import PlanarHom.SurfaceBooleanNullspaceCode
import PlanarHom.SurfaceBooleanQuotient

/-! NEW finite-coordinate transport of the computed quotient basis. -/
namespace PlanarHom.SurfaceBooleanRows

def restrictVector (m : ℕ) : Vector →ₗ[ZMod 2] (Fin m→ZMod 2) :=
  LinearMap.pi (fun i => LinearMap.proj i.val)

def extendVector (m : ℕ) : (Fin m→ZMod 2) →ₗ[ZMod 2] Vector where
  toFun x i := if hi : i<m then x ⟨i,hi⟩ else 0
  map_add' x y := by ext i; by_cases hi : i<m <;> simp [hi]
  map_smul' c x := by ext i; by_cases hi : i<m <;> simp [hi]

@[simp] theorem restrictVector_apply (m : ℕ) (x : Vector) (i : Fin m) :
    restrictVector m x i=x i.val := rfl
@[simp] theorem extendVector_apply (m : ℕ) (x : Fin m→ZMod 2) (i : ℕ) :
    extendVector m x i=(if hi : i<m then x ⟨i,hi⟩ else 0) := rfl

@[simp] theorem restrict_extend (m : ℕ) (x : Fin m→ZMod 2) :
    restrictVector m (extendVector m x)=x := by ext i; simp

theorem extend_injective (m : ℕ) : Function.Injective (extendVector m) := by
  intro x y h
  have he := congrArg (restrictVector m) h
  simpa using he

theorem extend_restrict (m : ℕ) (x : Vector) (h : Bounded m x) :
    extendVector m (restrictVector m x)=x := by
  funext i
  by_cases hi : i<m
  · simp [hi]
  · simp [hi,h i (Nat.le_of_not_gt hi)]

theorem value_eq_extend (shape r : Row) (h : r.length≤shape.length) :
    value r=extendVector shape.length (finiteValue shape.length r) :=
  (extend_restrict _ _ (value_bounded _ _ h)).symm

theorem inputSpan_eq_extend (shape : Row) (rs : List Row)
    (hw : ∀r∈rs,r.length≤shape.length) :
    inputSpan rs=(finiteSpan shape rs).map (extendVector shape.length) := by
  rw [inputSpan,finiteSpan_eq,Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact ⟨finiteValue shape.length r,List.mem_map.mpr ⟨r,hr,rfl⟩,(value_eq_extend shape r (hw r hr)).symm⟩
  · rintro ⟨y,hy,hx⟩
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hy
    exact ⟨r,hr,(value_eq_extend shape r (hw r hr)).trans hx⟩

theorem extend_mem_inputSpan_iff (shape : Row) (rs : List Row)
    (hw : ∀r∈rs,r.length≤shape.length) (x : Fin shape.length→ZMod 2) :
    extendVector shape.length x∈inputSpan rs ↔ x∈finiteSpan shape rs := by
  rw [inputSpan_eq_extend shape rs hw]
  constructor
  · rintro ⟨y,hy,he⟩
    have hyx := extend_injective shape.length he
    exact hyx ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem inputSpan_bounded (shape : Row) (rs : List Row)
    (hw : ∀r∈rs,r.length≤shape.length) (x : Vector) (hx : x∈inputSpan rs) :
    Bounded shape.length x := by
  rw [inputSpan_eq_extend shape rs hw] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  intro i hi
  simp [show ¬i<shape.length by omega]

def finiteQuotientEncode (shape : Row) (faces cycles : List Row) :
    (Fin shape.length→ZMod 2) →ₗ[ZMod 2] (Fin (quotientRows faces cycles).length→ZMod 2) :=
  (quotientEncode faces cycles).comp (extendVector shape.length)

def finiteQuotientLift (shape : Row) (faces cycles : List Row) :
    (Fin (quotientRows faces cycles).length→ZMod 2) →ₗ[ZMod 2] (Fin shape.length→ZMod 2) :=
  (restrictVector shape.length).comp (quotientLift faces cycles)

theorem finiteQuotientEncode_lift (shape : Row) (faces cycles : List Row)
    (hw : ∀r∈cycles,r.length≤shape.length) (hsub : inputSpan faces ≤ inputSpan cycles)
    (x : Fin (quotientRows faces cycles).length→ZMod 2) :
    finiteQuotientEncode shape faces cycles (finiteQuotientLift shape faces cycles x)=x := by
  change quotientEncode faces cycles (extendVector shape.length
    (restrictVector shape.length (quotientLift faces cycles x)))=x
  rw [extend_restrict _ _ (inputSpan_bounded shape cycles hw _ (quotientLift_mem faces cycles hsub x))]
  exact quotientEncode_lift faces cycles x

theorem finiteQuotient_kernel (shape : Row) (faces cycles : List Row)
    (hf : ∀r∈faces,r.length≤shape.length) (hc : ∀r∈cycles,r.length≤shape.length)
    (x : Fin shape.length→ZMod 2) (hx : x∈finiteSpan shape cycles) :
    finiteQuotientEncode shape faces cycles x=0 ↔ x∈finiteSpan shape faces := by
  change quotientEncode faces cycles (extendVector shape.length x)=0 ↔ _
  rw [quotientEncode_kernel faces cycles _ ((extend_mem_inputSpan_iff shape cycles hc x).mpr hx),
    extend_mem_inputSpan_iff shape faces hf x]

end PlanarHom.SurfaceBooleanRows
