import PlanarHom.FisherCubicRowCycles
import PlanarHom.RotationDartRelabel

/-! NEW inherited triangle rotation for an arbitrary cubic port enumeration.
The actual local edge direction flips are computed from the three port labels. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E : Type*} [DecidableEq (Dart E)]
variable (p : (V×Fin 3)≃(E×Bool)) (R : RotationRows (cubicOriginal p))

 def cubicCornerEquiv : Dart E≃V×Fin 3 :=
  (R.rotation.trans R.rotation).trans (cubicVertexEquiv p)

 def cubicCornerFlip (a : Dart E) : Bool :=
  decide ((cubicVertexEquiv p a).2≠triangle.src (cubicCornerEquiv p R a).2)

 theorem cubicCorner_first (a : Dart E) :
    (cubicCornerEquiv p R a).1=(cubicVertexEquiv p a).1 :=
  (cubicVertexEquiv_next_host p R (R.rotation a)).trans (cubicVertexEquiv_next_host p R a)

 theorem cubicCorner_reorient [Fintype E] (a : Dart E) :
    (if cubicCornerFlip p R a then triangle.dst (cubicCornerEquiv p R a).2
      else triangle.src (cubicCornerEquiv p R a).2)=(cubicVertexEquiv p a).2 ∧
    (if cubicCornerFlip p R a then triangle.src (cubicCornerEquiv p R a).2
      else triangle.dst (cubicCornerEquiv p R a).2)=(cubicVertexEquiv p (R.rotation a)).2 := by
  have h := cubic_corner_endpoints p R a
  change ((cubicVertexEquiv p a).2=triangle.src (cubicCornerEquiv p R a).2 ∧
    (cubicVertexEquiv p (R.rotation a)).2=triangle.dst (cubicCornerEquiv p R a).2) ∨
      ((cubicVertexEquiv p a).2=triangle.dst (cubicCornerEquiv p R a).2 ∧
       (cubicVertexEquiv p (R.rotation a)).2=triangle.src (cubicCornerEquiv p R a).2) at h
  rcases h with ⟨hi,hj⟩|⟨hi,hj⟩
  · have hf : cubicCornerFlip p R a=false := by simp only [cubicCornerFlip,hi,ne_self_iff_false,decide_false]
    rw [hf]
    exact ⟨hi.symm,hj.symm⟩
  · have hf : cubicCornerFlip p R a=true := decide_eq_true (by rw [hi]; exact (triangle_distinct_endpoints _).symm)
    rw [hf]
    exact ⟨hi.symm,hj.symm⟩

 def cubicEdgeEquiv : (E⊕Dart E)≃(E⊕(V×Fin 3)) := Equiv.sumCongr (Equiv.refl E) (cubicCornerEquiv p R)

 def cubicEdgeFlip : E⊕Dart E→Bool := Sum.elim (fun _=>false) (cubicCornerFlip p R)

 def cubicDartEquiv : Dart (E⊕Dart E)≃Dart (E⊕(V×Fin 3)) :=
  twistedDartEquiv (cubicEdgeEquiv p R) (cubicEdgeFlip p R)

 theorem cubicDart_host [Fintype E] (d : Dart (E⊕Dart E)) :
    ((cubicDecoration p).dartPair (cubicDartEquiv p R d)).1=
      cubicVertexEquiv p ((polygonGraph R).dartPair d).1 := by
  rcases d with ⟨e,b⟩
  cases e with
  | inl e =>
      cases b <;> rfl
  | inr a =>
      have h := cubicCorner_reorient p R a
      have hh := cubicCorner_first p R a
      have hh' : (cubicCornerEquiv p R a).1=(cubicVertexEquiv p (R.rotation a)).1 :=
        (cubicVertexEquiv_next_host p R (R.rotation a))
      cases b <;> cases hf : cubicCornerFlip p R a <;>
        simp only [hf,Bool.false_eq_true,if_false,if_true] at h <;>
        simp only [cubicDartEquiv,twistedDartEquiv,Equiv.coe_fn_mk,cubicEdgeEquiv,
          Equiv.sumCongr_apply,Sum.map_inr,cubicEdgeFlip,Sum.elim_inr,Bool.false_xor,Bool.true_xor,
          hf,Bool.not_false,Bool.not_true,polygonGraph,cubicDecoration,dartPair,Bool.false_eq_true,if_false,if_true] <;>
        apply Prod.ext
      all_goals first
        | exact hh'
        | exact hh
        | exact h.1
        | exact h.2

 def cubicRelabel [Fintype E] : DartRelabel (polygonGraph R) (cubicDecoration p) where
  vertex := cubicVertexEquiv p
  dart := cubicDartEquiv p R
  reverse := twistedDartEquiv_reverse _ _
  host := cubicDart_host p R

 def cubicInheritedRows [Fintype E] : RotationRows (cubicDecoration p) :=
  (cubicRelabel p R).rows (polygonRows R)

 theorem cubicOriginal_incident (v : V) : ∃a : Dart E,((cubicOriginal p).dartPair a).1=v := by
  obtain ⟨a,ha⟩ := (cubicVertexEquiv p).surjective (v,0)
  exact ⟨a,by rw [←cubicVertexEquiv_host,ha]⟩

 theorem cubicInherited_euler [Fintype V] [Fintype E]
    (h : Fintype.card V+count R.facePerm=Fintype.card E+2) :
    Fintype.card (V×Fin 3)+count (cubicInheritedRows p R).facePerm=
      Fintype.card (E⊕(V×Fin 3))+2 :=
  (cubicRelabel p R).euler (polygonRows R) (polygon_euler R (cubicOriginal_incident p) h)

end PlanarHom.Fisher
