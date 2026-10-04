import PlanarHom.RadialPottsNumericProgram
import Mathlib.Data.List.OfFn

/-! Literal endpoint agreement between the materialized numeric program and
the independently defined typed radial assembly. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPotts.Numeric
open Complexity Assembly MultiGraph RadialPottsTile
variable {m k : ℕ}

 def rotationCode (rotation : Equiv.Perm (Medial.Dart (Fin m))) : List ℕ :=
  List.ofFn (fun d : Fin (2*m) => dartIndex (rotation.symm ((dartIndexEquiv m).symm d)))

 def input (rotation : Equiv.Perm (Medial.Dart (Fin m))) (k : ℕ) : Input := (m,k,rotationCode rotation)

 @[simp] theorem rotationCode_getD (rotation : Equiv.Perm (Medial.Dart (Fin m))) (d : Medial.Dart (Fin m)) :
    (rotationCode rotation).getD (dartIndex d) 0=dartIndex (rotation.symm d) := by
  rw [← dartIndexEquiv_val]
  rw [List.getD_eq_getElem _ _ (by simpa [rotationCode] using (dartIndexEquiv m d).isLt)]
  simp only [rotationCode,List.getElem_ofFn]
  change dartIndex (rotation.symm ((dartIndexEquiv m).symm (dartIndexEquiv m d)))=_
  rw [Equiv.symm_apply_apply]

 theorem whiteName_eq (e : Fin m) (w : White k) :
    whiteName k e.val w.1.val w.2.val=(vertexIndexEquiv m k (.inl (e,w))).val := by
  simp [whiteName,whiteIndex,Nat.add_assoc]

 theorem switchedName_eq (e : Fin m) (w : White k) :
    switchedName k e.val w.1.val w.2.val=(vertexIndexEquiv m k (.inl (e,switch w))).val := by
  unfold switchedName switch
  split_ifs <;> simp [vertexIndexEquiv_white,whiteIndex,whiteName,Nat.add_assoc]

 theorem portName_eq (rotation : Equiv.Perm (Medial.Dart (Fin m))) (e : Fin m) (p : Port k) :
    portName (input rotation k) e.val p.1.val p.2.val=
      (vertexIndexEquiv m k (.inr (portImage rotation e p))).val := by
  rcases p with ⟨s,a⟩
  have h₀ := rotationCode_getD rotation (e,false)
  have h₁ := rotationCode_getD rotation (e,true)
  simp only [dartIndex,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at h₀ h₁
  simp only [List.getD_eq_getElem?_getD] at h₀ h₁
  fin_cases s <;>
    simp [portName,input,portImage,oddBit,endBit,vertexIndexEquiv_port,dartIndex,reverseLane,h₀,h₁,Nat.add_assoc]

 theorem longEntry_eq (rotation : Equiv.Perm (Medial.Dart (Fin m))) (e : Fin m) (f : Long k) :
    longEntry (input rotation k) e.val f.1.val f.2.1.val f.2.2.val=
      ((vertexIndexEquiv m k ((graph rotation k).src (e,.inl f))).val,
       ((vertexIndexEquiv m k ((graph rotation k).dst (e,.inl f))).val,0)) := by
  change (whiteName k e.val f.1.val _,_) = _
  apply Prod.ext
  · exact whiteName_eq e (longLeft f)
  · dsimp only [Prod.snd]
    congr 1
    by_cases h : f.1.val+1<k
    · simpa [longEntry,input,Assembly.graph,RadialPottsTile.graph,embed,longRight,h] using
        whiteName_eq e (⟨⟨f.1.val+1,h⟩,⟨f.2.1.val*(2*(f.1.val+1)+1)+2*f.2.2.val+1,by
          have := (longRight (k:=k) f); have hs := f.2.1.isLt; have ha := f.2.2.isLt
          have := Nat.mul_le_mul_right (2*(f.1.val+1)+1) (show f.2.1.val≤3 by omega)
          change _<8*(f.1.val+1)+4
          omega⟩⟩ : White k)
    · have ha : f.2.2.val<k := by have := f.1.isLt; have := f.2.2.isLt; omega
      simpa [longEntry,input,Assembly.graph,RadialPottsTile.graph,embed,longRight,h] using
        portName_eq rotation e (f.2.1,⟨f.2.2.val,ha⟩)

 theorem shortEntry_eq (rotation : Equiv.Perm (Medial.Dart (Fin m))) (e : Fin m)
    (f : HalfShort k) (b : Bool) :
    shortEntry k e.val f.1.val f.2.val b=
      ((vertexIndexEquiv m k ((graph rotation k).src (e,.inr (f,b)))).val,
       ((vertexIndexEquiv m k ((graph rotation k).dst (e,.inr (f,b)))).val,1)) := by
  cases b
  · change (switchedName k e.val f.1.val (2*f.2.val),
      (switchedName k e.val f.1.val (2*f.2.val+1),1))=_
    exact Prod.ext (switchedName_eq e (evenWhite f)) (Prod.ext (switchedName_eq e (oddWhite f)) rfl)
  · exact Prod.ext (whiteName_eq e (oddWhite f)) (Prod.ext (whiteName_eq e (nextWhite f)) rfl)
end PlanarHom.RadialPotts.Numeric
