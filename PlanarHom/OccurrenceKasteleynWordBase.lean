import PlanarHom.OccurrencePfaffianPairExchange
import Mathlib.Tactic

/-! NEW reconstruction: endpoint-word signs from the literal crossing sign.
The even cyclic shift is derived from the proved four-endpoint exchange identity. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
variable {V : Type*} [LinearOrder V]

def pairWord (ps : List (V × V)) : List V := ps.flatMap (fun p => [p.1,p.2])
def normalizePair (p : V × V) : V × V := (min p.1 p.2,max p.1 p.2)
def orderSign (a b : V) : ℤ := endpointOrderSign a b

def orientedPairSign (ps : List (V × V)) : ℤ :=
  pairingSign (ps.map normalizePair).toFinset * (ps.map (fun p => orderSign p.1 p.2)).prod

def pairChunks : List V → List (V × V)
  | a :: b :: xs => (a,b) :: pairChunks xs
  | _ => []
def wordSign (xs : List V) : ℤ := orientedPairSign (pairChunks xs)

@[simp] theorem pairWord_nil : pairWord ([] : List (V × V)) = [] := rfl
@[simp] theorem pairWord_cons (p : V × V) (ps) :
    pairWord (p::ps) = p.1::p.2::pairWord ps := rfl
@[simp] theorem pairWord_append (ps qs : List (V × V)) :
    pairWord (ps++qs) = pairWord ps ++ pairWord qs := by simp [pairWord]
@[simp] theorem pairWord_length (ps : List (V × V)) :
    (pairWord ps).length = 2*ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]; omega
@[simp] theorem pairChunks_pairWord (ps : List (V × V)) : pairChunks (pairWord ps)=ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [pairChunks,ih]
@[simp] theorem wordSign_pairWord (ps : List (V × V)) : wordSign (pairWord ps)=orientedPairSign ps := by
  simp [wordSign]
theorem fst_mem_pairWord {p : V × V} {ps : List (V × V)} (h:p∈ps) : p.1∈pairWord ps := by
  exact List.mem_flatMap.mpr ⟨p,h,by simp⟩
theorem snd_mem_pairWord {p : V × V} {ps : List (V × V)} (h:p∈ps) : p.2∈pairWord ps := by
  exact List.mem_flatMap.mpr ⟨p,h,by simp⟩
@[simp] theorem orderSign_sq (a b : V) : orderSign a b ^ 2 = 1 := by
  unfold orderSign endpointOrderSign; split_ifs <;> norm_num
@[simp] theorem orderSign_prod_sq (ps : List (V × V)) :
    (ps.map (fun p=>orderSign p.1 p.2)).prod ^ 2=1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [mul_pow,ih]
theorem pairingSign_normalize_eq_wordSign (ps : List (V × V)) (_hn:(pairWord ps).Nodup) :
    pairingSign (ps.map normalizePair).toFinset =
      wordSign (pairWord ps) * (ps.map (fun p=>orderSign p.1 p.2)).prod := by
  rw [wordSign_pairWord,orientedPairSign,mul_assoc,←pow_two,orderSign_prod_sq,mul_one]

theorem normalizePair_eq_ordered (a b : V) : normalizePair (a,b)=orderedEndpointPair a b := by
  by_cases h:a<b
  · simp [normalizePair,orderedEndpointPair,h,min_eq_left h.le,max_eq_right h.le]
  · have hh:=le_of_not_gt h
    simp [normalizePair,orderedEndpointPair,h,min_eq_right hh,max_eq_left hh]
@[simp] theorem normalizePair_reverse (a b : V) : normalizePair (b,a)=normalizePair (a,b) := by
  simp [normalizePair,min_comm,max_comm]
theorem orderSign_reverse {a b : V} (h:a≠b) : orderSign b a = -orderSign a b := by
  rcases lt_or_gt_of_ne h with h|h <;> simp [orderSign,endpointOrderSign,h,not_lt_of_gt h]
theorem orientedPairSign_perm {ps qs : List (V × V)} (h:ps.Perm qs) :
    orientedPairSign ps=orientedPairSign qs := by
  unfold orientedPairSign
  have he : (ps.map normalizePair).toFinset=(qs.map normalizePair).toFinset := by
    ext x; simp only [List.mem_toFinset]; exact (h.map normalizePair).mem_iff
  rw [he,(h.map (fun p=>orderSign p.1 p.2)).prod_eq]
theorem orientedPairSign_reverse (a b : V) (ps : List (V × V)) (h:a≠b) :
    orientedPairSign ((b,a)::ps) = -orientedPairSign ((a,b)::ps) := by
  simp only [orientedPairSign,List.map_cons,List.toFinset_cons,List.prod_cons,
    normalizePair_reverse,orderSign_reverse h]
  ring

theorem pairWord_nodup_endpoints {ps : List (V × V)} (hn:(pairWord ps).Nodup)
    {p:V×V} (hp:p∈ps) : p.1≠p.2 := by
  have h := (List.nodup_flatMap.mp hn).1 p hp
  simpa using h


end PlanarHom.MultiGraph
