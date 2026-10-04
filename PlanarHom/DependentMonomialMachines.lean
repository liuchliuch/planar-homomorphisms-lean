import PlanarHom.DependentFieldPowerMachines
import PlanarHom.ListDecompositionMachines
import PlanarHom.ExponentProductSemantics

/-! Fixed-width monomial circuits with literal dependent-field bases and capped exponents. -/
noncomputable section
namespace PlanarHom.DependentMonomialMachines
open Complexity
open scoped BigOperators

/-- Only a fixed number of actual list-tail projections is used. -/
theorem fp_getD {A : Type} (e : BitEncoding A) (d : A) (i : ℕ) :
    FP e.list e (fun xs => xs.getD i d) := by
  induction i with
  | zero => exact (ListDecompositionMachines.fp_headD e d).congr (fun xs => by cases xs <;> rfl)
  | succ i ih =>
    exact ((ListDecompositionMachines.fp_tail e d).comp ih).congr
      (fun xs => by cases xs <;> simp)

variable {X : Type} (ex : BitEncoding X) (K : X → Type)
variable [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
variable (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
local notation "e" => DependentFieldListMachines.fieldEncoding K dimension basis
local notation "ev" => DependentFieldCodecs.sigma ex e
local notation "es" => DependentFieldCodecs.pair ex e
variable {D : Type} (ed : BitEncoding D) (x : D → X)

 theorem fp_finset_product {ι : Type} [DecidableEq ι]
    (hmul : FP es ev (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩))
    (hone : FP ex ev (fun x => ⟨x,1⟩)) (hx : FP ed ex x)
    (s : Finset ι) (f : ι → ∀ d, K (x d))
    (hf : ∀ i ∈ s, FP ed ev (fun d => ⟨x d,f i d⟩)) :
    FP ed ev (fun d => ⟨x d,∏ i ∈ s,f i d⟩) := by
  induction s using Finset.induction_on with
  | empty => exact (hx.comp hone).congr (fun d => by simp)
  | @insert i s hi ih =>
    have ha := hf i (by simp)
    have hs := ih (fun j hj => hf j (by simp [hj]))
    exact ((DependentEncodingMachines.fp_pair ex e e ha hs).comp hmul).congr
      (fun d => by simp [hi])

/-- Arbitrary exponent words are clipped at an explicit unary cap, so this is total FP. -/
theorem fp_monomial {t : ℕ} (c : ℕ) (hc : ∀ x, dimension x ≤ c)
    (hpresentation : FP ex BitEncoding.rat.list (fun x => UniformFieldPresentationHeights.presentationList (basis x)))
    (hmul : FP es ev (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩))
    (hone : FP ex ev (fun x => ⟨x,1⟩))
    (A : ∀ d, Fin t → K (x d)) (m : D → ℕ) (r : D → List ℕ)
    (hA : FP ed (DependentFieldCodecs.sigma ex (fun x => (e x).vector t)) (fun d => ⟨x d,A d⟩))
    (hm : FP ed BitEncoding.unaryNat m) (hr : FP ed BitEncoding.nat.list r) :
    FP ed ev (fun d => ⟨x d,∏ i, A d i ^ min (m d) ((r d).getD i.val 0)⟩) := by
  have hx := hA.comp (DependentEncodingMachines.fp_parameter ex (fun x => (e x).vector t))
  apply fp_finset_product ex K dimension basis ed x hmul hone hx Finset.univ
  intro i _
  have ha := hA.comp (DependentEncodingMachines.fp_coordinate ex e t i)
  have hn := (hm.pair (hr.comp (fp_getD BitEncoding.nat 0 i.val))).comp ⟨BoundedUnaryMachines.computer⟩
  exact (hn.pair ha).comp (DependentFieldPowerMachines.fp_power ex K dimension basis c hc hpresentation hmul hone)

/-- On weak exponent lists the cap is exact, including m = 0 and t = 0. -/
theorem clipped_eq {t : ℕ} {L : Type} [Field L] (A : Fin t → L) (m : ℕ) (xs : List ℕ)
    (hxs : xs ∈ ExponentVectors.weak t m) :
    (∏ i, A i ^ min m (xs.getD i.val 0)) = ExponentProductSemantics.value A xs := by
  apply Finset.prod_congr rfl
  intro i _
  have hi : i.val < xs.length := by rw [((ExponentVectors.mem_weak t m xs).mp hxs).1]; exact i.isLt
  have hm : xs.getD i.val 0 ≤ m := by
    rw [List.getD_eq_getElem _ _ hi]
    exact ExponentVectors.coordinate_le hxs (List.getElem_mem hi)
  rw [min_eq_right hm]

end PlanarHom.DependentMonomialMachines
