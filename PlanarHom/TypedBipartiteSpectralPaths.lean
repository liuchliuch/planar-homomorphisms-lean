import PlanarHom.PrescribedDomainStretch

/-! Same-side selected paths with private vertices restricted to their actual
side. The selected matrix is supported on that side; arbitrary other matrices
are untouched. No ambient full-domain label is used. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.Complexity.MixedCode
variable {C R : Type} [Fintype C] [CommSemiring R]

/-- Adding fresh domain records has no effect when every nonzero summand
already satisfies those records. Unlike `evaluate_withFreshDomains`, the unary
need not be one on the ambient color space. -/
theorem evaluate_withFreshDomains_of_binary_support {a u : ℕ}
    (g : MixedCode) (hg : g.Valid a u) (oldVertices : ℕ) (label : Fin u)
    (M : Fin a → Matrix C C R) (U : Fin u → C → R) (w : C → R)
    (hsupport : ∀ σ : Fin g.vertices → C,
      (g.edges.map (binaryValue g.vertices a M σ)).prod ≠ 0 →
      ∀ v : Fin g.vertices, oldVertices ≤ v.val → U label (σ v)=1) :
    (g.withFreshDomains oldVertices label.val).evaluate
      (withFreshDomains_valid g hg oldVertices label.val label.isLt) M U w =
      g.evaluate hg M U w := by
  unfold evaluate withFreshDomains
  apply Finset.sum_congr rfl
  intro σ _
  rw [List.map_append, List.prod_append]
  by_cases hz : (g.edges.map (binaryValue g.vertices a M σ)).prod=0
  · simp only [hz,mul_zero,zero_mul]
  · have hp : (((List.range (g.vertices-oldVertices)).map
        (fun j => (oldVertices+j,label.val))).map
        (unaryValue g.vertices u U σ)).prod=1 := by
      apply List.prod_eq_one
      intro x hx
      obtain ⟨entry,hentry,rfl⟩ := List.mem_map.mp hx
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hentry
      have hj' := List.mem_range.mp hj
      have hv : oldVertices+j<g.vertices := by omega
      rw [unaryValue,dif_pos ⟨hv,label.isLt⟩]
      exact hsupport σ hz ⟨oldVertices+j,hv⟩ (Nat.le_add_right _ _)
    rw [hp,mul_one]

/-- Every private path vertex is the source of its next selected segment,
including when the original selected edge was a loop. -/
theorem stretchLabel_fresh_source {a b u : ℕ}
    (g : MixedCode) (hg : g.Valid a u) (selected replacement n : ℕ)
    (hr : replacement<b)
    (hkeep : ∀ e∈g.edges,e.2.2≠selected→e.2.2<b)
    (v : Fin (g.stretchLabel selected replacement n).vertices) (hv : g.vertices≤v.val) :
    ∃ e∈(g.stretchLabel selected replacement n).edges,
      e.1=v.val ∧ e.2.2=replacement := by
  let G := g.selectedGraph selected
  have hv' : v.val-g.vertices < G.edges.length*n := by
    have h := v.isLt
    change v.val < g.vertices+G.edges.length*n at h
    omega
  let p : Fin G.edges.length × Fin n := finProdFinEquiv.symm ⟨v.val-g.vertices,hv'⟩
  let k : Fin (n+1) := ⟨p.2.val+1,by omega⟩
  let e := ((G.stretchEndpoints n (p.1,k)).1,
    (G.stretchEndpoints n (p.1,k)).2,replacement)
  refine ⟨e,?_,?_,rfl⟩
  · have h := List.get_mem (g.stretchLabel selected replacement n).edges
      (g.stretchLabelEdgeEquiv selected replacement n (.inl (p.1,k)))
    rw [stretchLabel_get_left] at h
    exact h
  · change (G.stretchEndpoints n (p.1,k)).1=v.val
    simp only [GraphCode.stretchEndpoints,k,Nat.add_eq_zero_iff,Nat.one_ne_zero,
      and_false,↓reduceDIte,Nat.add_sub_cancel,GraphCode.stretchInternal]
    have he : finProdFinEquiv p = ⟨v.val-g.vertices,hv'⟩ := Equiv.apply_symm_apply _ _
    have he' : (finProdFinEquiv p).val=v.val-g.vertices := congrArg Fin.val he
    change g.vertices+(finProdFinEquiv p).val=v.val
    omega

/-- The emitted private-side indicators equal one on every nonzero path
assignment. Only the selected source matrix has a support condition. -/
theorem evaluate_stretchLabel_withFreshDomains_of_support {a b u : ℕ}
    (g : MixedCode) (hg : g.Valid a u) (selected n : ℕ) (replacement : Fin b)
    (hkeep : ∀ e∈g.edges,e.2.2≠selected→e.2.2<b) (label : Fin u)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R) (w : C → R)
    (hsupport : ∀ c d, M replacement c d ≠ 0 → U label c=1) :
    ((g.stretchLabel selected replacement.val n).withFreshDomains g.vertices label.val).evaluate
      (withFreshDomains_valid _ (g.stretchLabel_valid hg selected replacement.val n replacement.isLt hkeep)
        g.vertices label.val label.isLt) M U w =
    (g.stretchLabel selected replacement.val n).evaluate
      (g.stretchLabel_valid hg selected replacement.val n replacement.isLt hkeep) M U w := by
  apply evaluate_withFreshDomains_of_binary_support
  intro σ hprod v hv
  obtain ⟨e,he,hs,hl⟩ := g.stretchLabel_fresh_source hg selected replacement.val n
    replacement.isLt hkeep v hv
  have hb := (g.stretchLabel_valid hg selected replacement.val n replacement.isLt hkeep).1 e he
  have hn : binaryValue (g.stretchLabel selected replacement.val n).vertices b M σ e ≠ 0 := by
    intro hz
    apply hprod
    exact List.prod_eq_zero (List.mem_map.mpr ⟨e,he,hz⟩)
  simp only [binaryValue,hb.1,hb.2.1,hb.2.2,and_self,↓reduceDIte] at hn
  have hl' : (⟨e.2.2,hb.2.2⟩ : Fin b)=replacement := Fin.ext hl
  have hs' : (⟨e.1,hb.1⟩ : Fin (g.stretchLabel selected replacement.val n).vertices)=v := Fin.ext hs
  rw [hl',hs'] at hn
  exact hsupport _ _ hn

end PlanarHom.Complexity.MixedCode
