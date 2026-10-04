import PlanarHom.ZeroOneBasicStructure
import PlanarHom.SupportBlockSemantics

/-! NEW finite relation classification. When any two neighbors have identical
rows, each connected zero-one component is a looped clique, a complete
bipartite graph, or a single zero vertex. Repeated colors are retained. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.ZeroOneDifunctionalComponents
open RootedRestriction ZeroOneBasicStructure
variable {C : Type} [Fintype C]
variable (A : Matrix C C ℝ) (hs : ∀i j,A i j=A j i)
variable (h01 : ∀i j,A i j=0 ∨ A i j=1)
variable (hrows : ∀i j k,A i j≠0→A i k≠0→A j=A k)

include hrows in
theorem reachable_rows (a b : C) (hab : A a b≠0) {u v : C}
    (p : (colorSupport A hs).Walk u v) (hu : A u=A a ∨ A u=A b) :
    A v=A a ∨ A v=A b := by
  have hba : A b a≠0 := by simpa only [hs b a] using hab
  induction p with
  | nil => exact hu
  | @cons u v w huv p ih =>
    apply ih
    rcases hu with hu|hu
    · right
      apply hrows a v b _ hab
      simpa only [←congrFun hu v] using huv.2
    · left
      apply hrows b v a _ hba
      simpa only [←congrFun hu v] using huv.2

include h01 hrows in
theorem component_basic (c : (colorSupport A hs).ConnectedComponent) :
    BasicZeroOneComponent (fun i j : c.supp=>A i.val j.val) := by
  obtain ⟨a,ha⟩ := c.nonempty_supp
  have hreach (v : c.supp) : (colorSupport A hs).Reachable a v.val :=
    SimpleGraph.ConnectedComponent.exact (ha.trans v.property.symm)
  by_cases hn : ∃b,A a b≠0
  · obtain ⟨b,hab⟩ := hn
    have hb : b∈c.supp := component_colorClosed A hs c a ha b hab
    have hab1 : A a b=1 := (h01 a b).resolve_left hab
    have hba1 : A b a=1 := (hs b a).trans hab1
    have hpairs (v : c.supp) : A v.val=A a ∨ A v.val=A b := by
      obtain ⟨p⟩ := hreach v
      exact reachable_rows A hs hrows a b hab p (Or.inl rfl)
    by_cases he : A a=A b
    · left
      refine ⟨⟨⟨a,ha⟩⟩,?_⟩
      intro i j
      have hi : A i.val=A a := (hpairs i).elim id (fun h=>h.trans he.symm)
      have hj : A j.val=A b := (hpairs j).elim (fun h=>h.trans he) id
      calc
        A i.val j.val = A a j.val := congrFun hi _
        _ = A j.val a := hs _ _
        _ = A b a := congrFun hj _
        _ = 1 := hba1
    · right; left
      have haa : A a a=0 := by
        by_contra haa
        exact he (hrows a a b haa hab)
      have hbb : A b b=0 := by
        by_contra hbb
        exact he ((hrows b b a hbb (by simpa only [hs b a] using hab)).symm)
      let side : c.supp→Bool := fun v=>decide (A v.val=A a)
      have hsa : side ⟨a,ha⟩=true := by simp [side]
      have hsb : side ⟨b,hb⟩=false := by simp [side,Ne.symm he]
      refine ⟨side,?_,?_⟩
      · intro t
        cases t
        · exact ⟨⟨b,hb⟩,hsb⟩
        · exact ⟨⟨a,ha⟩,hsa⟩
      · intro i j
        rcases hpairs i with hi|hi <;> rcases hpairs j with hj|hj
        · have hv : A i.val j.val=0 := by rw [congrFun hi,hs a j.val,congrFun hj,haa]
          simp [side,hi,hj,hv]
        · have hv : A i.val j.val=1 := by rw [congrFun hi,hs a j.val,congrFun hj,hba1]
          simp [side,hi,hj,Ne.symm he,hv]
        · have hv : A i.val j.val=1 := by rw [congrFun hi,hs b j.val,congrFun hj,hab1]
          simp [side,hi,hj,Ne.symm he,hv]
        · have hv : A i.val j.val=0 := by rw [congrFun hi,hs b j.val,congrFun hj,hbb]
          simp [side,hi,hj,Ne.symm he,hv]
  · have hz : ∀b,A a b=0 := by simpa only [not_exists,not_not] using hn
    have he (v : c.supp) : a=v.val := by
      obtain ⟨p⟩ := hreach v
      cases p with
      | nil => rfl
      | cons had p => exact False.elim (had.2 (hz _))
    right; right
    refine ⟨⟨⟨a,ha⟩⟩,⟨fun i j=>Subtype.ext ((he i).symm.trans (he j))⟩,?_⟩
    funext i j
    change A i.val j.val=0
    rw [←he i,hz]

end PlanarHom.ZeroOneDifunctionalComponents
