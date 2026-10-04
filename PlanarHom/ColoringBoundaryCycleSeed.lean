import PlanarHom.RotationFaceCycleDuality
import PlanarHom.FinitePermutationCycleCount
import Mathlib.GroupTheory.Perm.Fin

/-! NEW literal initial boundary-cycle seed for the framed-canvas splice fold.
The two face cycles are derived from the actual two-dart rows, not assumed. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringBoundaryCycleSeed
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles

 def graph (N:ℕ) : MultiGraph (Fin N) (Fin N) where
   src e:=e
   dst e:=finRotate N e

 def row (N:ℕ) (v:Fin N) : List (Dart (Fin N)) :=
   [(v,true),((finRotate N).symm v,false)]

 def rows (N:ℕ) : RotationRows (graph N) where
   row:=row N
   nodup v:=by simp [row]
   mem v a:=by
     rcases a with ⟨e,b⟩
     cases b
     · simp only [row,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq,Bool.false_eq_true,and_false,false_or,and_true]
       change e=(finRotate N).symm v ↔ finRotate N e=v
       exact (finRotate N).eq_symm_apply
     · simp [row,graph,MultiGraph.dartPair]

 theorem rotation_true (N:ℕ) (e:Fin N) : (rows N).rotation (e,true)=((finRotate N).symm e,false) := by
   change (row N e).formPerm (e,true)=_
   simp [row,List.formPerm_pair]

 theorem rotation_false (N:ℕ) (e:Fin N) : (rows N).rotation (e,false)=(finRotate N e,true) := by
   change (row N (finRotate N e)).formPerm (e,false)=_
   simp [row,List.formPerm_pair]

 theorem face_true (N:ℕ) (e:Fin N) : (rows N).facePerm (e,true)=(finRotate N e,true) := rotation_false N e
 theorem face_false (N:ℕ) (e:Fin N) : (rows N).facePerm (e,false)=((finRotate N).symm e,false) := rotation_true N e

 def directionPerm (N:ℕ) (b:Bool) : Equiv.Perm (Fin N) := if b then finRotate N else (finRotate N).symm

 theorem face_apply (N:ℕ) (e:Fin N) (b:Bool) :
     (rows N).facePerm (e,b)=(directionPerm N b e,b) := by cases b <;> exact (by first | exact face_false N e | exact face_true N e)

 theorem face_pow (N:ℕ) (k:ℕ) (e:Fin N) (b:Bool) :
     ((rows N).facePerm^k) (e,b)=((directionPerm N b^k) e,b) := by
   induction k with
   | zero => rfl
   | succ k ih => simp only [pow_succ',Equiv.Perm.mul_apply,ih,face_apply]

 theorem rotate_sameCycle (N:ℕ) (hN:2≤N) (a b:Fin N) : (finRotate N).SameCycle a b := by
   apply (isCycle_finRotate_of_le hN).sameCycle
   all_goals apply Equiv.Perm.mem_support.mp; rw [support_finRotate_of_le hN]; exact Finset.mem_univ _

 theorem direction_sameCycle (N:ℕ) (hN:2≤N) (b:Bool) (e f:Fin N) : (directionPerm N b).SameCycle e f := by
   cases b
   · exact (rotate_sameCycle N hN e f).inv
   · exact rotate_sameCycle N hN e f

 theorem face_sameCycle_iff (N:ℕ) (hN:2≤N) (a b:Dart (Fin N)) :
     (rows N).facePerm.SameCycle a b ↔ a.2=b.2 := by
   rcases a with ⟨e,a⟩
   rcases b with ⟨f,b⟩
   constructor
   · intro h
     obtain ⟨k,hk⟩:=h.exists_nat_pow_eq
     rw [face_pow] at hk
     have hh:=congrArg (fun x:Dart (Fin N)=>x.2) hk
     exact hh
   · intro he
     change a=b at he
     subst b
     obtain ⟨k,hk⟩:=(direction_sameCycle N hN a e f).exists_nat_pow_eq
     refine ⟨(k:ℤ),?_⟩
     rw [zpow_natCast,face_pow,hk]

 def faceEquiv (N:ℕ) (hN:2≤N) : (rows N).Face≃Bool where
   toFun:=Quotient.lift (fun a=>a.2) (fun a b h=>(face_sameCycle_iff N hN a b).mp h)
   invFun b:=Quotient.mk _ (⟨0,by omega⟩,b)
   left_inv q:=by
     induction q using Quotient.inductionOn with
     | h a => exact Quotient.sound ((face_sameCycle_iff N hN _ _).mpr rfl)
   right_inv b:=rfl

 theorem face_count (N:ℕ) (hN:2≤N) : count (rows N).facePerm=2 := by
   change Nat.card (rows N).Face=2
   rw [Nat.card_congr (faceEquiv N hN)]
   simp only [Nat.card_eq_fintype_card,Fintype.card_bool]

 theorem connected (N:ℕ) (hN:2≤N) : ∀a b,(graph N).componentSetoid Finset.univ a b := by
   intro a b
   obtain ⟨k,hk⟩:=(rotate_sameCycle N hN a b).exists_nat_pow_eq
   have hw:∀k:ℕ,(graph N).componentSetoid Finset.univ a ((finRotate N^k) a) := by
     intro k
     induction k with
     | zero => exact Relation.EqvGen.refl _
     | succ k ih =>
       rw [pow_succ',Equiv.Perm.mul_apply]
       exact Relation.EqvGen.trans _ _ _ ih
         (Relation.EqvGen.rel _ _ ⟨(finRotate N^k) a,Finset.mem_univ _,rfl,rfl⟩)
   simpa only [hk] using hw k

 theorem euler (N:ℕ) (hN:2≤N) :
     Nat.card (Fin N)+count (rows N).facePerm=Nat.card (Fin N)+2 := by rw [face_count N hN]

 def marker (N:ℕ) (v:Fin N) : Dart (Fin N) := ((finRotate N).symm v,true)

 theorem marker_step (N:ℕ) (v:Fin N) :
     (rows N).facePerm (marker N v)=marker N (finRotate N v) := by
   simp only [marker,face_true,Equiv.apply_symm_apply,Equiv.symm_apply_apply]

 theorem row_ends_closing (N:ℕ) (v:Fin N) :
     (rows N).row v=[(v,true),reversePerm (Fin N) (marker N v)] := rfl

end PlanarHom.ColoringBoundaryCycleSeed
