import PlanarHom.SurfaceRotationFacePotentials
import PlanarHom.FisherPolygonEuler

/-! NEW actual homology kernel of the Fisher polygon replacement. A closed
chain with zero original-edge coordinates is a sum of the literal polygon
face boundaries. This will turn quotient representatives into real matchings. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

theorem polygon_cycle_equation (c : (polygonRows R).cycleSpace) (a : Dart E) :
    c.val (.inl a.1)+c.val (.inr a)+c.val (.inr (R.rotation.symm a))=0 := by
  have hh : ((polygonGraph R).coboundaryMatrix (ZMod 2)).transpose.mulVec c.val=0 := c.property
  have ha:=congrFun hh a
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,coboundaryMatrix,polygonGraph,
    Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,id_eq] at ha
  simp only [Equiv.apply_eq_iff_eq_symm_apply,sub_mul,ite_mul,one_mul,zero_mul,
    Finset.sum_sub_distrib,Finset.sum_ite_eq',sub_eq_add_neg,ZMod.neg_eq_self_mod_two] at ha
  rcases a with ⟨e,b⟩
  cases b <;> simpa [sub_mul,add_mul,Finset.sum_add_distrib,ite_mul,add_assoc] using ha

theorem polygon_cycle_internal_constant (c : (polygonRows R).cycleSpace)
    (hz : ∀e,c.val (.inl e)=0) (a : Dart E) :
    c.val (.inr (R.rotation.symm a))=c.val (.inr a) := by
  have hh:=polygon_cycle_equation R c a
  rw [hz,zero_add,add_eq_zero_iff_eq_neg,ZMod.neg_eq_self_mod_two] at hh
  exact hh.symm

def polygonKernelDartPotential (c : (polygonRows R).cycleSpace) : Dart (E⊕Dart E)→ZMod 2
  | (.inl _,_) => 0
  | (.inr a,true) => 0
  | (.inr a,false) => c.val (.inr a)

theorem polygonKernelDartPotential_face (c : (polygonRows R).cycleSpace)
    (hz : ∀e,c.val (.inl e)=0) (d : Dart (E⊕Dart E)) :
    polygonKernelDartPotential R c ((polygonRows R).facePerm d)=polygonKernelDartPotential R c d := by
  rcases d with ⟨e,b⟩
  cases e with
  | inl e =>
    change polygonKernelDartPotential R c ((polygonRows R).facePerm (polygonExternal (e,b)))=_
    rw [polygonFace_external]
    rfl
  | inr a =>
    cases b
    · rw [polygonFace_incoming]
      exact polygon_cycle_internal_constant R c hz a
    · change polygonKernelDartPotential R c ((polygonRows R).facePerm (polygonOutgoing a))=_
      rw [polygonFace_outgoing]
      rfl

theorem polygonKernelDartPotential_sameCycle (c : (polygonRows R).cycleSpace)
    (hz : ∀e,c.val (.inl e)=0) {a b : Dart (E⊕Dart E)}
    (hab : (polygonRows R).facePerm.SameCycle a b) :
    polygonKernelDartPotential R c a=polygonKernelDartPotential R c b := by
  obtain ⟨k,hk⟩:=hab.exists_nat_pow_eq
  have hi : ∀k,polygonKernelDartPotential R c ((polygonRows R).facePerm^[k] a)=polygonKernelDartPotential R c a := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply',polygonKernelDartPotential_face R c hz,ih]
  simpa only [Equiv.Perm.iterate_eq_pow,hk] using (hi k).symm

def polygonKernelFacePotential (c : (polygonRows R).cycleSpace)
    (hz : ∀e,c.val (.inl e)=0) : (polygonRows R).Face→ZMod 2 :=
  Quotient.lift (polygonKernelDartPotential R c) (fun _ _ h=>polygonKernelDartPotential_sameCycle R c hz h)

/-- Zero external coordinates force the actual homology class to vanish. -/
theorem polygon_homology_zero_of_external_zero (c : (polygonRows R).cycleSpace)
    (hz : ∀e,c.val (.inl e)=0) : (polygonRows R).homologyClass c=0 := by
  apply ((polygonRows R).homologyClass_eq_zero_iff c).mpr
  refine ⟨polygonKernelFacePotential R c hz,?_⟩
  funext e
  rw [(polygonRows R).dualGraph.coboundaryMatrix_apply]
  cases e with
  | inl e =>
    change (0:ZMod 2)-0=c.val (.inl e)
    simpa using (hz e).symm
  | inr a =>
    change 0-c.val (.inr a)=c.val (.inr a)
    rw [zero_sub,ZMod.neg_eq_self_mod_two]

end PlanarHom.Fisher
