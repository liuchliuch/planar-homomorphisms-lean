import PlanarHom.FreshDomainOccurrenceMachines
import PlanarHom.PrescribedDomainTyping
import PlanarHom.SelectedStretchPlanarity

/-! Exact intrinsic full-domain metadata for new path vertices. Existing domain
assignments are retained literally; adding these indicators has factor one. -/
noncomputable section
namespace PlanarHom.Complexity.MixedCode
open scoped BigOperators

theorem withFreshDomains_planar {a u : ℕ} (g : MixedCode) (hg : g.PlanarValid a u)
    (oldVertices label : ℕ) (hl : label<u) : (g.withFreshDomains oldVertices label).PlanarValid a u :=
  ⟨withFreshDomains_valid g hg.1 oldVertices label hl, hg.2⟩

theorem evaluate_withFreshDomains {C R : Type} [Fintype C] [CommSemiring R]
    {a u : ℕ} (g : MixedCode) (hg : g.Valid a u) (oldVertices : ℕ) (label : Fin u)
    (M : Fin a → Matrix C C R) (U : Fin u → C → R) (w : C → R)
    (hU : ∀ c, U label c=1) :
    (g.withFreshDomains oldVertices label.val).evaluate
      (withFreshDomains_valid g hg oldVertices label.val label.isLt) M U w = g.evaluate hg M U w := by
  unfold evaluate withFreshDomains
  apply Finset.sum_congr rfl
  intro σ _
  rw [List.map_append, List.prod_append]
  have hprod : (((List.range (g.vertices-oldVertices)).map (fun j => (oldVertices+j,label.val))).map
      (unaryValue g.vertices u U σ)).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨entry,hentry,rfl⟩ := List.mem_map.mp hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hentry
    have hj' := List.mem_range.mp hj
    have hv : oldVertices+j<g.vertices := by omega
    rw [unaryValue, dif_pos ⟨hv,label.isLt⟩]
    exact hU _
  rw [hprod, mul_one]

end PlanarHom.Complexity.MixedCode

namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode
variable {u d : ℕ}

def extendAssignment {oldV newV : ℕ} (δ : Fin oldV → Fin d) (full : Fin d) : Fin newV → Fin d :=
  fun v => if h : v.val<oldV then δ ⟨v.val,h⟩ else full

@[simp] theorem extendAssignment_old {oldV newV : ℕ} (δ : Fin oldV → Fin d) (full : Fin d)
    (v : Fin newV) (hv : v.val<oldV) : extendAssignment δ full v=δ ⟨v.val,hv⟩ := by
  simp [extendAssignment,hv]

@[simp] theorem extendAssignment_new {oldV newV : ℕ} (δ : Fin oldV → Fin d) (full : Fin d)
    (v : Fin newV) (hv : oldV≤v.val) : extendAssignment δ full v=full := by
  simp [extendAssignment,not_lt.mpr hv]

/-- The original ordered metadata prefix followed by one full-domain label per
new vertex is exactly the required new domain encoding. -/
theorem domainOccurrences_extend (g H : MixedCode) (hV : g.vertices≤H.vertices)
    (δ : Fin g.vertices → Fin d) (full : Fin d) :
    domainOccurrences (unaryTypes:=u) H (extendAssignment δ full) =
      domainOccurrences (unaryTypes:=u) g δ ++
        (List.range (H.vertices-g.vertices)).map (fun j => (g.vertices+j,u+full.val)) := by
  apply List.ext_getElem
  · simp only [domainOccurrences,List.length_ofFn,List.length_append,List.length_map,List.length_range]
    omega
  · intro i hi hj
    simp only [domainOccurrences,List.getElem_ofFn]
    by_cases h : i<g.vertices
    · rw [List.getElem_append_left (by simpa only [domainOccurrences,List.length_ofFn] using h)]
      simp [domainOccurrences,extendAssignment,h]
    · rw [List.getElem_append_right (by simpa only [domainOccurrences,List.length_ofFn] using Nat.le_of_not_gt h)]
      simp only [domainOccurrences,List.length_ofFn,List.getElem_map,List.getElem_range]
      simp [extendAssignment,h,Nat.add_sub_of_le (Nat.le_of_not_gt h)]

/-- Stretching preserves the original metadata prefix and appends exactly the
new full-domain records required by the source promise. -/
theorem stretchLabel_withDomains (g : MixedCode) (δ : Fin g.vertices → Fin d) (full : Fin d)
    (selected replacement n : ℕ) :
    ((withDomains (unaryTypes:=u) g δ).stretchLabel selected replacement n).withFreshDomains
      g.vertices (u+full.val) =
      withDomains (unaryTypes:=u) (g.stretchLabel selected replacement n) (extendAssignment δ full) := by
  have hv : g.vertices ≤ (g.stretchLabel selected replacement n).vertices := by
    rw [stretchLabel_vertices]
    omega
  have hd := domainOccurrences_extend (u:=u) g (g.stretchLabel selected replacement n) hv δ full
  change MixedCode.mk _ _ ((g.unaries ++ domainOccurrences (unaryTypes:=u) g δ) ++
      (List.range ((g.stretchLabel selected replacement n).vertices-g.vertices)).map
        (fun j => (g.vertices+j,u+full.val))) =
    MixedCode.mk _ _ (g.unaries ++ domainOccurrences (unaryTypes:=u)
      (g.stretchLabel selected replacement n) (extendAssignment δ full))
  rw [hd,List.append_assoc]
  rfl

end PlanarHom.PrescribedDomains
