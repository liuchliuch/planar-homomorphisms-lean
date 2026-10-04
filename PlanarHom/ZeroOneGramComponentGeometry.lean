import PlanarHom.ZeroOneGramBlockClassification

/-! NEW §7 support geometry. A positive square block forces all its original
neighbors into one partner block. Both restricted Gram matrices are positive
definite, so the two partner blocks have exactly the same cardinality. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.ZeroOneGramComponentGeometry
open RootedRestriction StrictTensorSupportBlocks ZeroOneGramBlockClassification
variable {q : ℕ}
variable (A : Matrix (Fin q) (Fin q) ℝ) (hs : ∀i j,A i j=A j i)
variable (hnn : ∀i j,0≤A i j)

abbrev graph := colorSupport (A*A) (square_symmetric A hs)

include hnn in
theorem neighbors_same_component (i j k : Fin q) (hij : A i j≠0) (hik : A i k≠0) :
    (graph A hs).connectedComponentMk j=(graph A hs).connectedComponentMk k := by
  by_cases hjk : j=k
  · exact congrArg _ hjk
  apply SimpleGraph.ConnectedComponent.sound
  apply SimpleGraph.Adj.reachable
  refine ⟨hjk,?_⟩
  have ht : 0<A j i*A i k :=
    mul_pos (by rw [hs j i]; exact lt_of_le_of_ne (hnn i j) hij.symm)
      (lt_of_le_of_ne (hnn i k) hik.symm)
  have hle : A j i*A i k≤(A*A) j k := by
    exact Finset.single_le_sum (fun x _=>mul_nonneg (hnn j x) (hnn x k)) (Finset.mem_univ i)
  exact ne_of_gt (lt_of_lt_of_le ht hle)

theorem common_neighbor
    (hb : Blocks (graph A hs) (A*A)) (c : (graph A hs).ConnectedComponent)
    (i x : c.supp) : ∃z,A i.val z≠0 ∧ A x.val z≠0 := by
  have hpos := (hb c).positive i x
  have hz : (∑z,A i.val z*A z x.val)≠0 := ne_of_gt hpos
  obtain ⟨z,_,hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  refine ⟨z,(mul_ne_zero_iff.mp hz).1,?_⟩
  simpa only [hs z x.val] using (mul_ne_zero_iff.mp hz).2

include hnn in
theorem partner_closed
    (hb : Blocks (graph A hs) (A*A)) (c : (graph A hs).ConnectedComponent)
    (i : c.supp) (j : Fin q) (hij : A i.val j≠0)
    (x : c.supp) (y : Fin q) (hxy : A x.val y≠0) :
    (graph A hs).connectedComponentMk y=(graph A hs).connectedComponentMk j := by
  obtain ⟨z,hiz,hxz⟩ := common_neighbor A hs hb c i x
  exact (neighbors_same_component A hs hnn x.val y z hxy hxz).trans
    (neighbors_same_component A hs hnn i.val z j hiz hij)

theorem sum_on_support {V : Type} [Fintype V] (S : Set V) [DecidablePred (fun v=>v∈S)] (f : V→ℝ)
    (hz : ∀v,v∉S→f v=0) : (∑v:S,f v.val)=∑v,f v := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun v=>v∈S) f
  have he : (∑v : {v // v∉S},f v.val)=0 := Finset.sum_eq_zero (fun v _=>hz v.val v.property)
  rw [he,add_zero] at h
  exact h

include hnn in
theorem paired_grams
    (hb : Blocks (graph A hs) (A*A)) (c : (graph A hs).ConnectedComponent)
    (i : c.supp) (j : Fin q) (hij : A i.val j≠0) :
    let d := (graph A hs).connectedComponentMk j
    let V : Matrix c.supp d.supp ℝ := fun x y=>A x.val y.val
    V*V.transpose=(fun x y=>(A*A) x.val y.val) ∧
      V.transpose*V=(fun x y=>(A*A) x.val y.val) := by
  dsimp only
  let d := (graph A hs).connectedComponentMk j
  have hj : j∈d.supp := rfl
  have hji : A j i.val≠0 := by simpa only [hs j i.val] using hij
  have hleft (x : c.supp) (y : Fin q) (hxy : A x.val y≠0) : y∈d.supp :=
    partner_closed A hs hnn hb c i j hij x y hxy
  have hright (x : d.supp) (y : Fin q) (hxy : A x.val y≠0) : y∈c.supp := by
    have he := partner_closed A hs hnn hb d ⟨j,hj⟩ i.val hji x y hxy
    exact he.trans i.property
  constructor
  · ext x y
    simp only [Matrix.mul_apply,Matrix.transpose_apply]
    simp_rw [hs y.val]
    apply sum_on_support d.supp (fun z=>A x.val z*A z y.val)
    intro z hz
    have he : A x.val z=0 := by by_contra he; exact hz (hleft x z he)
    rw [he,zero_mul]
  · ext x y
    simp only [Matrix.mul_apply,Matrix.transpose_apply]
    simp_rw [hs _ x.val]
    apply sum_on_support c.supp (fun z=>A x.val z*A z y.val)
    intro z hz
    have he : A x.val z=0 := by by_contra he; exact hz (hright x z he)
    rw [he,zero_mul]

include hnn in
theorem partner_card
    (hb : Blocks (graph A hs) (A*A)) (c : (graph A hs).ConnectedComponent)
    (i : c.supp) (j : Fin q) (hij : A i.val j≠0) :
    Fintype.card c.supp=Fintype.card ((graph A hs).connectedComponentMk j).supp := by
  let d := (graph A hs).connectedComponentMk j
  let V : Matrix c.supp d.supp ℝ := fun x y=>A x.val y.val
  have hg := paired_grams A hs hnn hb c i j hij
  have hpdX : (V*V.transpose).PosDef := by rw [hg.1]; exact (hb c).posDef
  have hpdY : (V.transpose*V).PosDef := by rw [hg.2]; exact (hb d).posDef
  rw [←Matrix.rank_of_isUnit _ hpdX.isUnit,←Matrix.rank_of_isUnit _ hpdY.isUnit,
    Matrix.rank_self_mul_transpose,Matrix.rank_transpose_mul_self]

end PlanarHom.ZeroOneGramComponentGeometry
