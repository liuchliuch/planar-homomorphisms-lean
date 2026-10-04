import PlanarHom.SignedNandNumericCompiler
import PlanarHom.SignedNandFormulaIdentity

/-! Removing repeated NAND edges is justified by exact idempotent products.
Signs occur only in the retained unary factors and are never discarded. -/
noncomputable section
open Classical
namespace PlanarHom.SignedNandNumeric
open SignedNandExactOneClause ListDedupMachines

theorem edgeTest_equivalence : Equivalence (ListDedupMachines.Rel edgeTest) := by
  have he : ∀x y,ListDedupMachines.Rel edgeTest x y ↔ x=y := by simp [ListDedupMachines.Rel,edgeTest]
  exact ⟨fun x => (he x x).mpr rfl,fun h => (he _ _).mpr ((he _ _).mp h).symm,
    fun h₁ h₂ => (he _ _).mpr (((he _ _).mp h₁).trans ((he _ _).mp h₂))⟩

theorem mem_edges_iff (f : ParsimoniousNorOneInThree.NumericFormula) (e : Edge) :
    e∈edges f ↔ ∃r∈rawEdges f,normalize r=e := by
  constructor
  · exact normalized_mem f e
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨q,hq,he⟩ := dedup_coverage edgeTest edgeTest_equivalence ((rawEdges f).map normalize)
      (normalize r) (List.mem_map.mpr ⟨r,hr,rfl⟩)
    have he' : normalize r=q := by simpa [ListDedupMachines.Rel,edgeTest] using he
    exact he' ▸ hq

theorem edges_nodup (f : ParsimoniousNorOneInThree.NumericFormula) : (edges f).Nodup := by
  have h := dedup_pairwise edgeTest edgeTest_equivalence ((rawEdges f).map normalize)
  exact h.imp (by intro a b h; simpa [ListDedupMachines.Rel,edgeTest] using h)

theorem normalize_idempotent (e : Edge) : normalize (normalize e)=normalize e := by
  by_cases h : e.2<e.1
  · have hn : ¬e.1<e.2 := by omega
    simp [normalize,h,hn]
  · simp [normalize,h]

theorem normalize_eq_or (e : Edge) : normalize e=e ∨ normalize e=(e.2,e.1) := by
  unfold normalize
  split <;> simp

theorem normalize_swap (e : Edge) : normalize (e.2,e.1)=normalize e := by
  by_cases h : e.2<e.1
  · have hn : ¬e.1<e.2 := by omega
    simp [normalize,h,hn]
  · by_cases h' : e.1<e.2
    · simp [normalize,h,h']
    · have he : e.1=e.2 := by omega
      rcases e with ⟨a,b⟩
      simp_all [normalize]

def edgeWeight (σ : ℕ → Bool) (e : Edge) : ℚ := nandWeight (σ e.1) (σ e.2)

theorem edgeWeight_normalize (σ : ℕ → Bool) (e : Edge) : edgeWeight σ (normalize e)=edgeWeight σ e := by
  rcases normalize_eq_or e with h | h
  · rw [h]
  · rw [h]
    simp [edgeWeight,nandWeight,Bool.and_comm]

theorem edgeWeight_idempotent (σ : ℕ → Bool) (e : Edge) : edgeWeight σ e*edgeWeight σ e=edgeWeight σ e := by
  simp only [edgeWeight,nandWeight]
  split <;> simp

private theorem list_indicator_product {A : Type} (xs : List A) (w : A → ℚ)
    (hw : ∀a∈xs,w a=0 ∨ w a=1) :
    (xs.map w).prod=if ∀a∈xs,w a=1 then 1 else 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have htail := ih (fun b hb => hw b (by simp [hb]))
    rcases hw a (by simp) with ha | ha
    · simp [ha,htail]
    · simp [ha,htail]

/-- Exact algebraic removal of all repeated unordered adjacencies. -/
theorem edge_product_eq_raw (f : ParsimoniousNorOneInThree.NumericFormula) (σ : ℕ → Bool) :
    ((edges f).map (edgeWeight σ)).prod=((rawEdges f).map (edgeWeight σ)).prod := by
  have hb (e : Edge) : edgeWeight σ e=0 ∨ edgeWeight σ e=1 := by
    simp only [edgeWeight,nandWeight]; split <;> simp
  rw [list_indicator_product _ _ (fun e _ => hb e),list_indicator_product _ _ (fun e _ => hb e)]
  have he : (∀e∈edges f,edgeWeight σ e=1) ↔ ∀e∈rawEdges f,edgeWeight σ e=1 := by
    constructor
    · intro h e he
      have hn := h (normalize e) ((mem_edges_iff f _).mpr ⟨e,he,rfl⟩)
      simpa only [edgeWeight_normalize] using hn
    · intro h e he
      obtain ⟨r,hr,rfl⟩ := normalized_mem f e he
      rw [edgeWeight_normalize]
      exact h r hr
  simp only [he]

end PlanarHom.SignedNandNumeric
