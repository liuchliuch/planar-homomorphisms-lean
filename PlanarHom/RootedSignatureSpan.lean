import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The finite weighted projection argument underlying source Lemma 3.5.
The coefficient field is the original ordered field, not a real extension. -/
noncomputable section
open scoped BigOperators
open Classical Matrix
namespace PlanarHom.RootedSignatureSpan
variable {K C J : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable [Fintype C] [Fintype J]

def pairing (w u v : C → K) : K := ∑ i, w i * u i * v i

def pairingMap (w u : C → K) : (C → K) →ₗ[K] K where
  toFun := pairing w u
  map_add' v z := by simp [pairing, mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [pairing, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem pairing_comm (w u v : C → K) : pairing w u v = pairing w v u := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem pairing_sum (w : C → K) (c : J → K) (f : J → C → K) (v : C → K) :
    pairing w (∑ j, c j • f j) v = ∑ j, c j * pairing w (f j) v := by
  rw [pairing_comm]
  change pairingMap w v (∑ j, c j • f j) = _
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [show pairingMap w v (f j) = pairing w (f j) v from pairing_comm w v (f j)]

theorem pairing_self_eq_zero (w u : C → K) (hw : ∀ i, 0 < w i)
    (h : pairing w u u = 0) : u = 0 := by
  have hn : ∀ i ∈ (Finset.univ : Finset C), 0 ≤ w i * u i * u i := by
    intro i _
    nlinarith [hw i, sq_nonneg (u i)]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp h
  funext i
  have hi := hz i (Finset.mem_univ i)
  have hmul : w i * (u i * u i) = 0 := by nlinarith [hi]
  have hu : u i * u i = 0 := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (hw i))
  simpa using (mul_self_eq_zero.mp hu)

def gram (w : C → K) (f : J → C → K) : Matrix J J K :=
  fun a b => pairing w (f a) (f b)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem gram_mulVec (w : C → K) (f : J → C → K) (c : J → K) (a : J) :
    (gram w f *ᵥ c) a = pairing w (f a) (∑ j, c j • f j) := by
  change (∑ j, pairing w (f a) (f j) * c j) = pairingMap w (f a) (∑ j, c j • f j)
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem gram_kernel (w : C → K) (hw : ∀ i, 0 < w i) (f : J → C → K)
    (hf : LinearIndependent K f) (c : J → K) (hc : gram w f *ᵥ c = 0) : c = 0 := by
  let v := ∑ j, c j • f j
  have hv : v = 0 := by
    apply pairing_self_eq_zero w v hw
    rw [show v = ∑ j, c j • f j from rfl, pairing_sum]
    apply Finset.sum_eq_zero
    intro j _
    have hj := congrFun hc j
    rw [gram_mulVec] at hj
    simp only [Pi.zero_apply] at hj
    rw [hj, mul_zero]
  exact funext (Fintype.linearIndependent_iff.mp hf c hv)

/-- Every linear functional on the finite signature span has a representation
by weighted pairings with the same basis signatures, in the original field. -/
theorem exists_coefficients (w : C → K) (hw : ∀ i, 0 < w i)
    (f : J → C → K) (hf : LinearIndependent K f) (target : C → K) :
    ∃ c : J → K, ∀ v ∈ Submodule.span K (Set.range f),
      pairing w target v = ∑ j, c j * pairing w (f j) v := by
  let g := (gram w f).mulVecLin
  have hg : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact gram_kernel w hw f hf c hc
  obtain ⟨c,hc⟩ := (LinearMap.surjective_of_injective hg) (fun j => pairing w (f j) target)
  refine ⟨c,?_⟩
  let lhs := pairingMap w target
  let rhs : (C → K) →ₗ[K] K := ∑ j, c j • pairingMap w (f j)
  have hEq : Set.EqOn lhs rhs (Set.range f) := by
    rintro _ ⟨a,rfl⟩
    have ha := congrFun hc a
    change (gram w f *ᵥ c) a = pairing w (f a) target at ha
    rw [gram_mulVec] at ha
    change pairing w target (f a) = _
    simp only [rhs, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [pairing_comm w target (f a), ← ha, pairing_comm, pairing_sum]
    rfl
  intro v hv
  simpa only [lhs, rhs, pairingMap, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk] using LinearMap.eqOn_span hEq hv

/-- Choose finitely many members of any signature family, then project onto
its span. The choice depends only on that fixed family and target functional. -/
theorem exists_family_coefficients {S : Type*} (w : C → K) (hw : ∀ i, 0 < w i)
    (f : S → C → K) (target : C → K) :
    ∃ n : ℕ, ∃ indices : Fin n → S, ∃ c : Fin n → K, ∀ s : S,
      pairing w target (f s) = ∑ j, c j * pairing w (f (indices j)) (f s) := by
  obtain ⟨b,hb,hspan,hli⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range f)
  choose indices hind using hb
  obtain ⟨c,hc⟩ := exists_coefficients w hw b hli target
  refine ⟨_,indices,c,?_⟩
  intro s
  simp only [hind]
  exact hc (f s) (hspan.symm ▸ Submodule.subset_span (Set.mem_range_self s))

end PlanarHom.RootedSignatureSpan
