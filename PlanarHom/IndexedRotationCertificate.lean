import PlanarHom.RadialPottsNumericVertices
import PlanarHom.FinitePermutationCycleCertificate
import PlanarHom.FinitePermutationCycleTransport

/-! Numeric certificates for complete vertex rotations and connected finite
occurrence graphs, using the literal endpoint numbering 2e and 2e+1. -/
noncomputable section
open Classical
namespace PlanarHom.IndexedRotationCertificate
open MultiGraph FinitePermutationCycles RadialPotts.Assembly

 def boolFlip : Equiv.Perm Bool := ⟨Bool.not,Bool.not,by intro b; cases b <;> rfl,by intro b; cases b <;> rfl⟩

 def flip (m : ℕ) : Equiv.Perm (Fin (2*m)) :=
  (dartIndexEquiv m).permCongr (Equiv.prodCongr (Equiv.refl (Fin m)) boolFlip)

 theorem flip_index (m : ℕ) (e : Fin m) (b : Bool) :
    flip m (dartIndexEquiv m (e,b))=dartIndexEquiv m (e,!b) := by
  simp [flip,boolFlip,Equiv.permCongr_apply]

 theorem flip_twice (m : ℕ) (d : Fin (2*m)) : flip m (flip m d)=d := by
  obtain ⟨⟨e,b⟩,rfl⟩ := (dartIndexEquiv m).surjective d
  rw [flip_index,flip_index]
  cases b <;> rfl

 theorem flip_value (m : ℕ) (d : Fin (2*m)) :
    (flip m d).val=if d.val%2=0 then d.val+1 else d.val-1 := by
  obtain ⟨⟨e,b⟩,rfl⟩ := (dartIndexEquiv m).surjective d
  rw [flip_index]
  cases b <;> simp [dartIndexEquiv_val,dartIndex] <;> omega

 def graph {n m : ℕ} (host : Fin (2*m) → Fin n) : MultiGraph (Fin n) (Fin m) where
  src e := host (dartIndexEquiv m (e,false))
  dst e := host (dartIndexEquiv m (e,true))

 theorem graph_host {n m : ℕ} (host : Fin (2*m) → Fin n) (d : Medial.Dart (Fin m)) :
    (graph host).dartVertex d=host (dartIndexEquiv m d) := by
  rcases d with ⟨e,b⟩
  cases b <;> rfl

 def rotation {m : ℕ} (P : Equiv.Perm (Fin (2*m))) : Equiv.Perm (Medial.Dart (Fin m)) :=
  (dartIndexEquiv m).symm.permCongr (P*flip m)

 theorem rotation_cycles {n m : ℕ} (host : Fin (2*m) → Fin n)
    (P : Equiv.Perm (Fin (2*m))) (C : LabelCertificate (P*flip m) (Fin n))
    (hc : C.label=host) (a b : Medial.Dart (Fin m)) :
    (rotation P).SameCycle a b ↔ (graph host).dartVertex a=(graph host).dartVertex b := by
  have ht := sameCycle_iff_of_step (rotation P) (P*flip m) (dartIndexEquiv m)
    (by intro a; simp [rotation,Equiv.permCongr_apply]) a b
  rw [ht,C.sameCycle_iff,hc,graph_host,graph_host]

 theorem graph_host_surjective {n m : ℕ} (host : Fin (2*m) → Fin n)
    (P : Equiv.Perm (Fin (2*m))) (C : LabelCertificate (P*flip m) (Fin n))
    (hc : C.label=host) : Function.Surjective (graph host).dartVertex := by
  intro v
  refine ⟨(dartIndexEquiv m).symm (C.root v),?_⟩
  rw [graph_host,Equiv.apply_symm_apply,←hc,C.root_label]

 structure ConnectivityCertificate {n m : ℕ} (G : MultiGraph (Fin n) (Fin m)) where
  root : Fin n
  parent : Fin n → Fin n
  parentEdge : Fin n → Fin m
  rank : Fin n → ℕ
  zero_root : ∀v,rank v=0 → v=root
  adjacent : ∀v,0<rank v →
    (G.src (parentEdge v)=v ∧ G.dst (parentEdge v)=parent v) ∨
    (G.dst (parentEdge v)=v ∧ G.src (parentEdge v)=parent v)
  decreases : ∀v,0<rank v → rank (parent v)<rank v

 theorem ConnectivityCertificate.reaches_root {n m : ℕ} {G : MultiGraph (Fin n) (Fin m)}
    (C : ConnectivityCertificate G) (v : Fin n) : G.componentSetoid Finset.univ v C.root := by
  suffices ∀r,∀v,C.rank v=r → G.componentSetoid Finset.univ v C.root from this _ v rfl
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro v hv
    by_cases hz : C.rank v=0
    · rw [C.zero_root v hz]
    · have hp := Nat.pos_of_ne_zero hz
      have he : G.componentSetoid Finset.univ v (C.parent v) := by
        rcases C.adjacent v hp with ⟨hs,ht⟩ | ⟨ht,hs⟩
        · exact Relation.EqvGen.rel _ _ ⟨C.parentEdge v,Finset.mem_univ _,hs,ht⟩
        · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
            ⟨C.parentEdge v,Finset.mem_univ _,hs,ht⟩)
      exact Relation.EqvGen.trans _ _ _ he
        (ih (C.rank (C.parent v)) (by have := C.decreases v hp; omega) _ rfl)

 theorem ConnectivityCertificate.connected {n m : ℕ} {G : MultiGraph (Fin n) (Fin m)}
    (C : ConnectivityCertificate G) (a b : Fin n) : G.componentSetoid Finset.univ a b :=
  Relation.EqvGen.trans _ _ _ (C.reaches_root a) (Relation.EqvGen.symm _ _ (C.reaches_root b))
end PlanarHom.IndexedRotationCertificate
