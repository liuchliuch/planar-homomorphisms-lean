import PlanarHom.SurfaceRotationHomology
import PlanarHom.FisherPolygonEuler

/-! NEW intrinsic capped-ribbon genus computed from literal permutation cycles.
Integrality follows from permutation signs; nonnegativity follows from actual
primal/dual incidence rank. No genus certificate is supplied. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceRotationGenus
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

 theorem reverse_sameCycle_iff (a b : Dart E) :
    (reversePerm E).SameCycle a b ↔ a.1=b.1 := by
  constructor
  · intro h
    obtain ⟨n,hn⟩:=h.exists_nat_pow_eq
    have hi:∀n,((reversePerm E)^[n] a).1=a.1 := by
      intro n
      induction n with
      | zero=>rfl
      | succ n ih=>simpa [Function.iterate_succ_apply',reversePerm] using ih
    have hh:=hi n
    rw [Equiv.Perm.iterate_eq_pow,hn] at hh
    exact hh.symm
  · rcases a with ⟨e,a⟩
    rcases b with ⟨f,b⟩
    intro h
    dsimp only at h
    subst f
    cases a <;> cases b
    · exact Equiv.Perm.SameCycle.rfl
    · exact Equiv.Perm.SameCycle.rfl.apply_right
    · exact Equiv.Perm.SameCycle.rfl.apply_right
    · exact Equiv.Perm.SameCycle.rfl

 theorem reverse_count : count (reversePerm E)=Fintype.card E :=
  count_eq_card_of_label (reversePerm E) Prod.fst (fun e=>⟨(e,true),rfl⟩) reverse_sameCycle_iff

 theorem incident_of_connected (root : Dart E) (hc : ∀u v,G.componentSetoid Finset.univ u v) :
    ∀v,∃a:Dart E,(G.dartPair a).1=v := by
  intro v
  let p:=fun u:V=>∃a:Dart E,(G.dartPair a).1=u
  have he:G.EdgeConstant Finset.univ p := by
    intro e he
    apply propext
    exact ⟨fun _=>⟨(e,false),rfl⟩,fun _=>⟨(e,true),rfl⟩⟩
  have h:=G.edgeConstant_respects Finset.univ p he (hc (G.dartPair root).1 v)
  exact Eq.mp h ⟨root,rfl⟩

 theorem euler_parity (hinc : ∀v,∃a:Dart E,(G.dartPair a).1=v) :
    Even (Fintype.card V+Fintype.card R.Face+Fintype.card E) := by
  have hs : (Equiv.Perm.sign R.facePerm:ℤ)=
      (Equiv.Perm.sign R.rotation:ℤ)*(Equiv.Perm.sign (reversePerm E):ℤ) := by
    change ((Equiv.Perm.sign (R.rotation*reversePerm E):ℤˣ):ℤ)=_
    rw [map_mul,Units.val_mul]
  rw [sign_coe_eq_pow_card_add_count,sign_coe_eq_pow_card_add_count,
    sign_coe_eq_pow_card_add_count,Fisher.rotation_count_of_incident R hinc,reverse_count] at hs
  have hf:count R.facePerm=Fintype.card R.Face := Nat.card_eq_fintype_card
  rw [hf] at hs
  simp only [Dart,Fintype.card_prod,Fintype.card_bool] at hs
  rw [Nat.mul_comm (Fintype.card E) 2] at hs
  norm_num [pow_add,pow_mul] at hs
  apply (neg_one_pow_eq_one_iff_even (show (-1:ℤ)≠1 by norm_num)).mp
  calc
    (-1:ℤ)^(Fintype.card V+Fintype.card R.Face+Fintype.card E)=
        (-1:ℤ)^(Fintype.card R.Face)*((-1:ℤ)^(Fintype.card V)*(-1:ℤ)^(Fintype.card E)) := by
      simp only [pow_add]
      ring
    _ = (-1:ℤ)^(Fintype.card R.Face)*(-1:ℤ)^(Fintype.card R.Face) := by rw [←hs]
    _ = 1 := by rw [←pow_add,←two_mul,pow_mul]; norm_num

 def genus : ℕ := (Fintype.card E+2-(Fintype.card V+Fintype.card R.Face))/2

 theorem hasGenus (root : Dart E) (hc : ∀u v,G.componentSetoid Finset.univ u v) :
    R.HasGenus (genus R) := by
  have hle:=R.euler_le root hc
  have he:=euler_parity R (incident_of_connected root hc)
  rw [Nat.even_iff] at he
  unfold RotationRows.HasGenus genus
  omega

 theorem genus_unique {h : ℕ} (hh:R.HasGenus h) : genus R=h := by
  unfold genus RotationRows.HasGenus at *
  omega

end PlanarHom.SurfaceRotationGenus
