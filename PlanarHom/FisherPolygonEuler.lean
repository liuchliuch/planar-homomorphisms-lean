import PlanarHom.FisherPolygonRotation
import PlanarHom.FinitePermutationArrowSubdivision

/-! NEW exact face permutation of polygon replacement: the old face arrows
are subdivided once, while the reversed old vertex cycles bound the polygons. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)]
variable [Fintype V] [Fintype E] (R : RotationRows G)

 def polygonDartEquiv : Dart (E⊕Dart E) ≃ ((Dart E⊕Dart E)⊕Dart E) where
  toFun
    | (.inl e,b) => .inl (.inl (e,b))
    | (.inr a,true) => .inl (.inr (reversePerm E a))
    | (.inr a,false) => .inr a
  invFun
    | .inl (.inl a) => polygonExternal a
    | .inl (.inr a) => polygonOutgoing (reversePerm E a)
    | .inr a => (.inr a,false)
  left_inv d := by
    rcases d with ⟨e,b⟩
    cases e with
    | inl e => rfl
    | inr a => cases b <;> simp [polygonOutgoing,reversePerm]
  right_inv d := by
    rcases d with (a|a)|a
    · rfl
    · simp [polygonOutgoing,reversePerm]
    · rfl

 theorem polygonFace_conjugacy (d : Dart (E⊕Dart E)) :
    polygonDartEquiv ((polygonRows R).facePerm d)=
      Equiv.sumCongr (subdivideArrows R.facePerm) R.rotation⁻¹ (polygonDartEquiv d) := by
  rcases d with ⟨e,b⟩
  cases e with
  | inl e =>
      change polygonDartEquiv ((polygonRows R).facePerm (polygonExternal (e,b)))=_
      rw [polygonFace_external]
      simp [polygonDartEquiv,polygonOutgoing,reversePerm,subdivideArrows]
  | inr a =>
      cases b
      · rw [polygonFace_incoming]
        rfl
      · change polygonDartEquiv ((polygonRows R).facePerm (polygonOutgoing a))=_
        rw [polygonFace_outgoing]
        simp [polygonDartEquiv,polygonExternal,polygonOutgoing,subdivideArrows,RotationRows.facePerm,reversePerm]

 theorem polygon_face_count : count (polygonRows R).facePerm=count R.facePerm+count R.rotation := by
  rw [count_semiconj _ _ polygonDartEquiv (polygonFace_conjugacy R),count_sumCongr,count_subdivideArrows,count_inv]

 theorem rotation_sameCycle_iff_host (a b : Dart E) :
    R.rotation.SameCycle a b ↔ (G.dartPair a).1=(G.dartPair b).1 := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hh := R.rotation_iterate_host a n
    simpa only [Equiv.Perm.iterate_eq_pow,hn] using hh.symm
  · intro h
    obtain ⟨n,hn⟩ := R.exists_rotation_iterate_of_sameHost a b h
    exact ⟨(n:ℤ),by simpa only [zpow_natCast,Equiv.Perm.iterate_eq_pow] using hn⟩

 theorem rotation_count_of_incident (hinc : ∀v : V,∃a : Dart E,(G.dartPair a).1=v) :
    count R.rotation=Fintype.card V := by
  exact count_eq_card_of_label R.rotation (fun a=>(G.dartPair a).1) hinc (rotation_sameCycle_iff_host R)

/-- Exact connected Euler transfer to the polygon replacement. For degree
three, this is the full triangle-decoration Euler step. -/
theorem polygon_euler (hinc : ∀v : V,∃a : Dart E,(G.dartPair a).1=v)
    (heuler : Fintype.card V+count R.facePerm=Fintype.card E+2) :
    Fintype.card (Dart E)+count (polygonRows R).facePerm=Fintype.card (E⊕Dart E)+2 := by
  rw [polygon_face_count,rotation_count_of_incident R hinc]
  simp only [Dart,Fintype.card_prod,Fintype.card_bool,Fintype.card_sum]
  omega

end PlanarHom.Fisher
