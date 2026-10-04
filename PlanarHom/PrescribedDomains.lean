import PlanarHom.MixedProductSemantics
import PlanarHom.MixedPlanarCode

/-!
# Exact fixed-domain representation by reserved intrinsic unary occurrences

The allowed family D is fixed data and the vertex assignment δ is retained.
The reserved indicator labels below encode those prescribed domains only.
This is a representation equivalence, not availability of arbitrary pinning.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode
attribute [local instance] Classical.propDecidable
variable {C R : Type} [Fintype C] [CommSemiring R]
variable {binaryTypes unaryTypes domainTypes : ℕ}

/-- The fixed prescribed-domain indicator. -/
def indicator (D : Set C) (c : C) : R := if c ∈ D then 1 else 0

def Allowed {V : Type} (D : Fin domainTypes → Set C) (δ : V → Fin domainTypes) (σ : V → C) : Prop :=
  ∀ v, σ v ∈ D (δ v)

theorem indicator_product {V : Type} [Fintype V] (D : Fin domainTypes → Set C)
    (δ : V → Fin domainTypes) (σ : V → C) :
    (∏ v, indicator (R := R) (D (δ v)) (σ v)) = if Allowed D δ σ then 1 else 0 := by
  classical
  by_cases h : Allowed D δ σ
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro v _
    exact if_pos (h v)
  · rw [if_neg h]
    have hn : ∃ v, σ v ∉ D (δ v) := by simpa [Allowed] using h
    obtain ⟨v, hv⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [indicator, hv])

/-- Extending the fixed unary language gives separate reserved domain labels. -/
def extendedUnaries (U : Fin unaryTypes → C → R) (D : Fin domainTypes → Set C) :
    Fin (unaryTypes + domainTypes) → C → R :=
  Fin.addCases U (fun d => indicator (D d))

/-- Domain occurrences are intrinsic metadata, one per existing vertex. -/
def domainOccurrences (g : MixedCode) (δ : Fin g.vertices → Fin domainTypes) : List (ℕ × ℕ) :=
  List.ofFn (fun v => (v.val, unaryTypes + (δ v).val))

/-- The encoded incidence graph is unchanged; only reserved domain metadata are appended. -/
def withDomains (g : MixedCode) (δ : Fin g.vertices → Fin domainTypes) : MixedCode :=
  ⟨g.vertices, g.edges, g.unaries ++ domainOccurrences (unaryTypes := unaryTypes) g δ⟩

theorem withDomains_valid (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (δ : Fin g.vertices → Fin domainTypes) :
    (withDomains (unaryTypes := unaryTypes) g δ).Valid binaryTypes (unaryTypes + domainTypes) := by
  refine ⟨hg.1, ?_⟩
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact ⟨(hg.2 e he).1, (hg.2 e he).2.trans_le (Nat.le_add_right _ _)⟩
  · obtain ⟨v, rfl⟩ := List.mem_ofFn.mp he
    exact ⟨v.isLt, Nat.add_lt_add_left (δ v).isLt _⟩

@[simp] theorem withDomains_underlying (g : MixedCode) (δ : Fin g.vertices → Fin domainTypes) :
    (withDomains (unaryTypes := unaryTypes) g δ).underlying = g.underlying := rfl

theorem withDomains_planar_iff (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (δ : Fin g.vertices → Fin domainTypes) :
    (withDomains (unaryTypes := unaryTypes) g δ).PlanarValid binaryTypes (unaryTypes + domainTypes) ↔
      g.PlanarValid binaryTypes unaryTypes := by
  simp only [MixedCode.PlanarValid, withDomains_valid g hg δ, true_and, withDomains_underlying, hg]

/-- Actual restricted-assignment semantics for fixed prescribed domains. -/
def evaluateRestricted (g : MixedCode) (_hg : g.Valid binaryTypes unaryTypes)
    (M : Fin binaryTypes → Matrix C C R) (U : Fin unaryTypes → C → R) (w : C → R)
    (D : Fin domainTypes → Set C) (δ : Fin g.vertices → Fin domainTypes) : R :=
  ∑ σ : Fin g.vertices → C, if Allowed D δ σ then
    (∏ v, w (σ v)) * (g.edges.map (binaryValue g.vertices binaryTypes M σ)).prod *
      (g.unaries.map (unaryValue g.vertices unaryTypes U σ)).prod else 0

/-- The reserved unary label of a vertex is exactly its prescribed indicator. -/
theorem domainOccurrences_product (g : MixedCode)
    (U : Fin unaryTypes → C → R) (D : Fin domainTypes → Set C)
    (δ : Fin g.vertices → Fin domainTypes) (σ : Fin g.vertices → C) :
    ((domainOccurrences (unaryTypes := unaryTypes) g δ).map
      (unaryValue g.vertices (unaryTypes + domainTypes) (extendedUnaries U D) σ)).prod =
        ∏ v, indicator (R := R) (D (δ v)) (σ v) := by
  simp only [domainOccurrences, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  apply Finset.prod_congr rfl
  intro v _
  have hbound : unaryTypes + (δ v).val < unaryTypes + domainTypes :=
    Nat.add_lt_add_left (δ v).isLt _
  simp only [unaryValue, v.isLt, hbound, and_self, ↓reduceDIte]
  change extendedUnaries U D (Fin.natAdd unaryTypes (δ v)) (σ v) = _
  rw [extendedUnaries, Fin.addCases_right]

/-- Original unary occurrences still refer to the same ordinary unary functions. -/
theorem originalUnaries_product (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (U : Fin unaryTypes → C → R) (D : Fin domainTypes → Set C) (σ : Fin g.vertices → C) :
    (g.unaries.map (unaryValue g.vertices (unaryTypes + domainTypes) (extendedUnaries U D) σ)).prod =
      (g.unaries.map (unaryValue g.vertices unaryTypes U σ)).prod := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  have hv := hg.2 e he
  have hbound : e.2 < unaryTypes + domainTypes := hv.2.trans_le (Nat.le_add_right _ _)
  simp only [unaryValue, hv.1, hv.2, hbound, and_self, ↓reduceDIte]
  change extendedUnaries U D (Fin.castAdd domainTypes ⟨e.2, hv.2⟩) (σ ⟨e.1, hv.1⟩) = _
  rw [extendedUnaries, Fin.addCases_left]

/-- Finite restricted sums are exactly sums weighted by the intrinsic domain indicators. -/
theorem sum_restricted_eq_indicators {V : Type} [Fintype V]
    (D : Fin domainTypes → Set C) (δ : V → Fin domainTypes) (f : (V → C) → R) :
    (∑ σ : {σ : V → C // Allowed D δ σ}, f σ.val) =
      ∑ σ : V → C, f σ * ∏ v, indicator (R := R) (D (δ v)) (σ v) := by
  have hs := Fintype.sum_subtype_add_sum_subtype (Allowed D δ)
    (fun σ : V → C => f σ * ∏ v, indicator (R := R) (D (δ v)) (σ v))
  have hyes : (∑ σ : {σ : V → C // Allowed D δ σ},
      f σ.val * ∏ v, indicator (R := R) (D (δ v)) (σ.val v)) =
      ∑ σ : {σ : V → C // Allowed D δ σ}, f σ.val := by
    apply Finset.sum_congr rfl
    intro σ _
    rw [indicator_product, if_pos σ.property, mul_one]
  have hno : (∑ σ : {σ : V → C // ¬Allowed D δ σ},
      f σ.val * ∏ v, indicator (R := R) (D (δ v)) (σ.val v)) = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    rw [indicator_product, if_neg σ.property, mul_zero]
  simpa only [hyes, hno, add_zero] using hs

/-- Exact representation of the original fixed-domain model, without adding pinning power. -/
theorem evaluate_withDomains (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes)
    (M : Fin binaryTypes → Matrix C C R) (U : Fin unaryTypes → C → R) (w : C → R)
    (D : Fin domainTypes → Set C) (δ : Fin g.vertices → Fin domainTypes) :
    (withDomains (unaryTypes := unaryTypes) g δ).evaluate (withDomains_valid g hg δ) M
      (extendedUnaries U D) w = evaluateRestricted g hg M U w D δ := by
  unfold evaluateRestricted evaluate withDomains
  apply Finset.sum_congr rfl
  intro σ _
  simp only [List.map_append, List.prod_append]
  rw [originalUnaries_product g hg U D σ, domainOccurrences_product g U D δ σ,
    indicator_product]
  split <;> simp_all [mul_assoc]

/-- Binary replication commutes with the original, unchanged prescribed domains. -/
theorem parallelLabel_withDomains (g : MixedCode) (δ : Fin g.vertices → Fin domainTypes)
    (selected s : ℕ) :
    (withDomains (unaryTypes := unaryTypes) g δ).parallelLabel selected s =
      withDomains (unaryTypes := unaryTypes) (g.parallelLabel selected s) δ := rfl

/-- Replication leaves every occurrence whose label is not selected untouched. -/
theorem repeatSelected_eq_of_false {A : Type} (test : A → Bool) (s : ℕ) (xs : List A)
    (h : ∀ x ∈ xs, test x = false) : repeatSelected test s xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [repeatSelected_cons, h x (List.mem_cons_self)]
    simpa using ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- Reserved intrinsic domain labels are never selected by an ordinary unary query. -/
theorem parallelUnaryLabel_withDomains (g : MixedCode) (δ : Fin g.vertices → Fin domainTypes)
    (selected s : ℕ) (hselected : selected < unaryTypes) :
    (withDomains (unaryTypes := unaryTypes) g δ).parallelUnaryLabel selected s =
      withDomains (unaryTypes := unaryTypes) (g.parallelUnaryLabel selected s) δ := by
  have hdom : repeatSelected (fun e : ℕ × ℕ => decide (e.2 = selected)) s
      (domainOccurrences (unaryTypes := unaryTypes) g δ) =
      domainOccurrences (unaryTypes := unaryTypes) g δ := by
    apply repeatSelected_eq_of_false
    intro e he
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp he
    simp only [decide_eq_false_iff_not]
    omega
  have ha : repeatSelected (fun e : ℕ × ℕ => decide (e.2 = selected)) s
      (g.unaries ++ domainOccurrences (unaryTypes := unaryTypes) g δ) =
      repeatSelected (fun e : ℕ × ℕ => decide (e.2 = selected)) s g.unaries ++
        domainOccurrences (unaryTypes := unaryTypes) g δ := by
    rw [repeatSelected, List.flatMap_append]
    change _ ++ repeatSelected _ _ _ = _
    rw [hdom]
    rfl
  cases g with
  | mk vertices edges unaries =>
    simp only [withDomains, parallelUnaryLabel] at ha ⊢
    exact congrArg (fun us => MixedCode.mk vertices edges us) ha

end PlanarHom.PrescribedDomains
