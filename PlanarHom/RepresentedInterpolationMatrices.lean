import PlanarHom.RepresentedPowerTable
import PlanarHom.RepresentedPositiveSequence

/-! Literal variable-order augmented interpolation matrix construction. Every
power is a fixed-alphabet word product; all other field operations have fixed
depth. The emitted table is square including the empty-node case. -/
noncomputable section
open Classical
namespace PlanarHom.RepresentedInterpolationMatrices
open Complexity RepresentedBit RepresentedPowerTable PairProjectionMachines
variable {K:Type} [Field K] (P:Presentation K) {t:ℕ} {A:Fin t→K}

def zero : P.Code := P.constant 0
def one : P.Code := P.constant 1

def entry (WA:WordProductMachine P A) (p:ℕ×Row P t) : P.Code := (WA.power (p.1,p.2.2.2)).val

theorem fp_entry (WA:WordProductMachine P A) :
    FP (BitEncoding.unaryNat.prod (encoding P t)) P.encoding (entry P WA) := by
  have h:FP (encoding P t) (wordEncoding t) (fun r=>r.2.2):=
    (fp_snd _ _).comp (fp_snd _ _)
  have hp:=((fp_fst BitEncoding.unaryNat (encoding P t)).pair
    ((fp_snd BitEncoding.unaryNat (encoding P t)).comp h)).comp WA.fp_power
  exact hp.transportOutput (fun _=>rfl)

def topRow (WA:WordProductMachine P A) (n:ℕ) (rs:List (Row P t)) : List P.Code :=
  rs.map (fun r=>entry P WA (n,r))++[zero P]

theorem fp_topRow (WA:WordProductMachine P A) :
    FP (BitEncoding.unaryNat.prod (encoding P t).list) P.encoding.list (fun p=>topRow P WA p.1 p.2) :=
  ((ListContextMachines.fp_mapWithContext _ _ _ _ (fp_entry P WA)).pair
    (fp_const _ P.encoding.list [zero P])).comp (ListMutationMachines.fp_append P.encoding)

def negTarget (ops:AddMulMachines P) (r:Row P t) : P.Code :=
  ops.mul (P.constant (-1),r.2.1.val)

theorem fp_negTarget (ops:AddMulMachines P) :
    FP (encoding P t) P.encoding (negTarget P ops) := by
  have h:FP (encoding P t) (validEncoding P) (fun r=>r.2.1):=
    (fp_snd _ _).comp (fp_fst _ _)
  have hv:FP (validEncoding P) P.encoding Subtype.val:=fp_code_view _ _ _ (fun _=>rfl)
  exact ((fp_const _ P.encoding (P.constant (-1))).pair (h.comp hv)).comp ops.fp_mul

def lastRow (ops:AddMulMachines P) (rs:List (Row P t)) : List P.Code :=
  rs.map (negTarget P ops)++[one P]

theorem fp_lastRow (ops:AddMulMachines P) :
    FP (encoding P t).list P.encoding.list (lastRow P ops) :=
  ((ListMapMachines.fp_map _ _ _ (fp_negTarget P ops)).pair
    (fp_const _ P.encoding.list [one P])).comp (ListMutationMachines.fp_append P.encoding)

def matrix (ops:AddMulMachines P) (WA:WordProductMachine P A) (rs:List (Row P t)) : List (List P.Code) :=
  positiveSequence (topRow P WA) (rs.length,rs)++[lastRow P ops rs]

theorem fp_matrix (ops:AddMulMachines P) (WA:WordProductMachine P A) :
    FP (encoding P t).list P.encoding.list.list (matrix P ops WA) := by
  have ht:=((ListUnaryLengthMachine.fp_length (encoding P t)).pair (fp_id (encoding P t).list)).comp
    (fp_positiveSequence (encoding P t).list P.encoding.list (topRow P WA) (fp_topRow P WA))
  have hsingle:FP P.encoding.list P.encoding.list.list (fun r=>[r]):=
    ((fp_id _).pair (fp_const _ P.encoding.list.list [])).comp (ListMutationMachines.fp_cons P.encoding.list)
  exact (ht.pair ((fp_lastRow P ops).comp hsingle)).comp (ListMutationMachines.fp_append P.encoding.list)

def rhs (ys:List P.Code) : List P.Code := ys++[zero P]

theorem fp_rhs : FP P.encoding.list P.encoding.list (rhs P) :=
  ((fp_id _).pair (fp_const _ P.encoding.list [zero P])).comp (ListMutationMachines.fp_append P.encoding)

def system (ops:AddMulMachines P) (WA:WordProductMachine P A) (p:List (Row P t)×List P.Code) :
    List (List P.Code)×List P.Code := (matrix P ops WA p.1,rhs P p.2)

theorem fp_system (ops:AddMulMachines P) (WA:WordProductMachine P A) :
    FP ((encoding P t).list.prod P.encoding.list) (P.encoding.list.list.prod P.encoding.list)
      (system P ops WA) :=
  ((fp_fst _ _).comp (fp_matrix P ops WA)).pair ((fp_snd _ _).comp (fp_rhs P))

@[simp] theorem matrix_length (ops:AddMulMachines P) (WA:WordProductMachine P A) (rs:List (Row P t)) :
    (matrix P ops WA rs).length=rs.length+1 := by simp [matrix,positiveSequence]

theorem matrix_row_length (ops:AddMulMachines P) (WA:WordProductMachine P A) (rs:List (Row P t))
    (r:List P.Code) (hr:r∈matrix P ops WA rs) : r.length=rs.length+1 := by
  simp only [matrix,List.mem_append,List.mem_singleton] at hr
  rcases hr with hr|rfl
  · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hr
    simp [topRow]
  · simp [lastRow]

theorem matrix_valid (ops:AddMulMachines P) (WA:WordProductMachine P A) (rs:List (Row P t))
    (r:List P.Code) (hr:r∈matrix P ops WA rs) (c:P.Code) (hc:c∈r) : P.valid c := by
  simp only [matrix,List.mem_append,List.mem_singleton] at hr
  rcases hr with hr|rfl
  · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hr
    simp only [topRow,List.mem_append,List.mem_singleton] at hc
    rcases hc with hc|rfl
    · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hc
      exact (WA.power _).property
    · exact P.constant_valid 0
  · simp only [lastRow,List.mem_append,List.mem_singleton] at hc
    rcases hc with hc|rfl
    · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hc
      exact ops.mul_valid _ _ (P.constant_valid _) r.2.1.property
    · exact P.constant_valid 1

theorem matrix_values (ops:AddMulMachines P) (WA:WordProductMachine P A) (rs:List (Row P t))
    (hword:∀r∈rs,(r.2.2.val.map (RepresentedExponentWords.symbol A)).prod=source P r) :
    (matrix P ops WA rs).map (List.map P.value)=
      ((List.range rs.length).map (fun i=>rs.map (fun r=>source P r^(i+1))++[0]))++
        [rs.map (fun r=> -target P r)++[1]] := by
  simp only [matrix,positiveSequence,List.map_append,List.map_map,List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply,topRow,List.map_append,List.map_map,List.map_singleton]
    congr 1
    · apply List.map_congr_left
      intro r hr
      exact (WA.power_value (i+1) r.2.2).trans (congrArg (fun x:K=>x^(i+1)) (hword r hr))
    · simp [zero]
  · congr 1
    simp only [lastRow,List.map_append,List.map_map,List.map_singleton]
    congr 1
    · apply List.map_congr_left
      intro r hr
      simp only [Function.comp_apply,negTarget,ops.mul_value _ _ (P.constant_valid _) r.2.1.property,
        P.constant_value,neg_one_mul,target,validValue]
    · simp [one]

end PlanarHom.RepresentedInterpolationMatrices
