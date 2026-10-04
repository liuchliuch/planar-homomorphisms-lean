import PlanarHom.ColoringEmitterLocalPatches
import PlanarHom.ColoringEmitterPrivateAddressTables

/-! NEW exact enumeration and address laws for the literal private complement.
Only the fixed finite macro tables are checked computationally. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open PositiveBlockProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Macro
 def exposed (k : Kind) : List ℕ := (ports k).flatMap (fun p=>[p.1,p.2.1,p.2.2])
 theorem privateVertices_filter (k : Kind) : privateVertices k=
     (List.range (vertexCount k)).filter (fun v=>!(exposed k).contains v) := by
   cases k <;> decide +kernel
 theorem privateVertices_nodup (k : Kind) : (privateVertices k).Nodup := by
   rw [privateVertices_filter]
   exact List.nodup_range.filter _
 theorem privateVertices_length (k : Kind) : (privateVertices k).length=privateCount k := by cases k <;> decide +kernel
 theorem privateVertices_bound (k : Kind) : ∀v∈privateVertices k,v<vertexCount k := by
   intro v hv
   rw [privateVertices_filter] at hv
   exact List.mem_range.mp (List.mem_filter.mp hv).1
end Macro

namespace LocalPatch

theorem exposed_eq_ports (s : CellShape) : Macro.exposed s.kind=
    List.ofFn (fun i : Fin (s.portCount*3)=>portNumber s (finProdFinEquiv.symm i)) := by
  cases s <;> decide +kernel

theorem exposed_mem_iff (s : CellShape) (v : ℕ) :
    v∈Macro.exposed s.kind ↔ ∃p:Port s,portNumber s p=v := by
  rw [exposed_eq_ports,List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨finProdFinEquiv.symm i,hi⟩
  · rintro ⟨p,hp⟩
    exact ⟨finProdFinEquiv p,by simpa using hp⟩

theorem private_mem_iff (s : CellShape) (v : NumericVertex s) :
    v.val∈Macro.privateVertices s.kind ↔ ∀p:Port s,portNumber s p≠v.val := by
  simp [Macro.privateVertices_filter,exposed_mem_iff,v.isLt]

theorem private_mem (s : CellShape) (w : Private s) : w.val.val∈Macro.privateVertices s.kind := by
  apply (private_mem_iff s w.val).mpr
  intro p hp
  exact w.property ⟨p,Fin.ext hp⟩

def privateMemberEquiv (s : CellShape) : Private s ≃ {v:ℕ // v∈Macro.privateVertices s.kind} where
  toFun w := ⟨w.val.val,private_mem s w⟩
  invFun v := ⟨⟨v.val,Macro.privateVertices_bound s.kind _ v.property⟩,by
    rintro ⟨p,hp⟩
    exact ((private_mem_iff s _).mp v.property p) (congrArg Fin.val hp)⟩
  left_inv w := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv v := by apply Subtype.ext; rfl

def privateEquiv (s : CellShape) : Private s ≃ Fin (Macro.privateCount s.kind) :=
  (privateMemberEquiv s).trans (((Macro.privateVertices_nodup s.kind).getEquiv (Macro.privateVertices s.kind)).symm.trans
    (finCongr (Macro.privateVertices_length s.kind)))

theorem privateEquiv_val (s : CellShape) (w : Private s) :
    (privateEquiv s w).val=Macro.privateRank s.kind w.val.val := by
  simp [privateEquiv,privateMemberEquiv,List.Nodup.getEquiv,Macro.privateRank,
    List.idxOf,Lean.Grind.beq_eq_decide_eq]

theorem port_address (s : CellShape) : ∀p:Port s,
    Macro.address s.kind (portNumber s p)=
      if p.1.val<Macro.inputCount s.kind then (0,p.1.val,p.2.val)
      else (1,p.1.val-Macro.inputCount s.kind,p.2.val) := by
  cases s <;> decide +kernel

theorem private_address_index (k : Kind) (i : Fin (Macro.privateVertices k).length) :
    Macro.address k ((Macro.privateVertices k).get i)=(2,i.val,0) := by
  apply Macro.privateAddressTable_valid k (((Macro.privateVertices k).get i),i.val)
  rw [Macro.privateAddressTable_eq]
  simp [List.mk_mem_zipIdx_iff_getElem?]

theorem private_address (s : CellShape) (w : Private s) :
    Macro.address s.kind w.val.val=(2,(privateEquiv s w).val,0) := by
  let e := (Macro.privateVertices_nodup s.kind).getEquiv (Macro.privateVertices s.kind)
  let i := e.symm (privateMemberEquiv s w)
  have hg : (Macro.privateVertices s.kind).get i=w.val.val :=
    congrArg Subtype.val (e.apply_symm_apply (privateMemberEquiv s w))
  have ha := private_address_index s.kind i
  rw [hg] at ha
  exact ha

end LocalPatch
end PlanarHom.ColoringEmitter
