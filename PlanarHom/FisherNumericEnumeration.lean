import PlanarHom.FisherCodeProgram
import PlanarHom.FisherExpansionGraph
import Mathlib.Data.List.NodupEquivFin

/-! NEW finite serialization lemmas used for the concrete Fisher incidence
bijections. Enumeration preserves all edge occurrences and ordered endpoints. -/
noncomputable section
open Classical
namespace PlanarHom.FisherNumericEnumeration
open Complexity MultiGraph
variable {V E : Type}

 def enumeratedCode (G : MultiGraph V E) (vs : List V) (es : List E) : MixedCode :=
  ⟨vs.length,es.map (fun e=>(vs.idxOf (G.src e),vs.idxOf (G.dst e),0)),[]⟩

 theorem enumerated_valid (G : MultiGraph V E) (vs : List V) (es : List E)
    (hvs : ∀v,v∈vs) : (enumeratedCode G vs es).Valid 1 0 := by
  constructor
  · intro a ha
    obtain ⟨e,_,rfl⟩:=List.mem_map.mp ha
    exact ⟨List.idxOf_lt_length_iff.mpr (hvs _),List.idxOf_lt_length_iff.mpr (hvs _),by dsimp; omega⟩
  · simp [enumeratedCode]

 def enumeratedIncidenceEquiv (G : MultiGraph V E) (vs : List V) (es : List E)
    (hv : vs.Nodup) (he : es.Nodup) (hvs : ∀v,v∈vs) (hes : ∀e,e∈es) :
    IncidenceEquiv G ((enumeratedCode G vs es).toMultiGraph (enumerated_valid G vs es hvs)) where
  vertex := (hv.getEquivOfForallMemList vs hvs).symm
  edge := ((he.getEquivOfForallMemList es hes).symm).trans (finCongr (by simp [enumeratedCode]))
  src_eq e := by
    apply Fin.ext
    simp [MixedCode.toMultiGraph,enumeratedCode,List.get_eq_getElem,List.getElem_idxOf,List.Nodup.getEquivOfForallMemList]
  dst_eq e := by
    apply Fin.ext
    simp [MixedCode.toMultiGraph,enumeratedCode,List.get_eq_getElem,List.getElem_idxOf,List.Nodup.getEquivOfForallMemList]

 def sigmaList {A : Type} {B : A→Type} (as : List A) (bs : ∀a,List (B a)) : List (Sigma B) :=
  as.flatMap (fun a=>(bs a).map (Sigma.mk a))

 theorem sigmaList_mem {A : Type} {B : A→Type} (as : List A) (bs : ∀a,List (B a)) (p : Sigma B) :
    p∈sigmaList as bs ↔ p.1∈as ∧ p.2∈bs p.1 := by
  rcases p with ⟨a,b⟩
  constructor
  · intro h
    obtain ⟨a',ha',hm⟩:=List.mem_flatMap.mp h
    obtain ⟨b',hb',he⟩:=List.mem_map.mp hm
    cases he
    exact ⟨ha',hb'⟩
  · rintro ⟨ha,hb⟩
    exact List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩

 theorem sigmaList_nodup {A : Type} {B : A→Type} (as : List A) (bs : ∀a,List (B a))
    (ha : as.Nodup) (hb : ∀a∈as,(bs a).Nodup) : (sigmaList as bs).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro a ha
    exact (hb a ha).map (fun x y h=>eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  · apply ha.imp
    intro a b hab x hx hy
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hx
    obtain ⟨j,_,hxy⟩:=List.mem_map.mp hy
    exact hab (congrArg Sigma.fst hxy).symm

 def finSigma (n : ℕ) (d : Fin n→ℕ) : List (Σv,Fin (d v)) :=
  sigmaList (List.finRange n) (fun v=>List.finRange (d v))

 theorem finSigma_mem (n : ℕ) (d : Fin n→ℕ) (p : Σv,Fin (d v)) : p∈finSigma n d := by
  rw [finSigma,sigmaList_mem]
  exact ⟨List.mem_finRange _,List.mem_finRange _⟩

 theorem finSigma_nodup (n : ℕ) (d : Fin n→ℕ) : (finSigma n d).Nodup :=
  sigmaList_nodup _ _ (List.nodup_finRange _) (fun _ _=>List.nodup_finRange _)

theorem idxOf_map_injective {A B : Type} (f : A→B) (hf : Function.Injective f) (xs : List A) (a : A) :
    (xs.map f).idxOf (f a)=xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.map_cons,List.idxOf_cons,Lean.Grind.beq_eq_decide_eq,hf.eq_iff,ih]

def codeIncidenceEquiv {c d : MixedCode} {bt ut : ℕ} (h : c=d)
    (hc : c.Valid bt ut) (hd : d.Valid bt ut) : IncidenceEquiv (c.toMultiGraph hc) (d.toMultiGraph hd) := by
  subst d
  exact ⟨Equiv.refl _,Equiv.refl _,fun _=>rfl,fun _=>rfl⟩

theorem codeIncidenceEquiv_edge_val {c d : MixedCode} {bt ut : ℕ} (h : c=d)
    (hc : c.Valid bt ut) (hd : d.Valid bt ut) (e : Fin c.edges.length) :
    ((codeIncidenceEquiv h hc hd).edge e).val=e.val := by subst d; rfl

theorem codeIncidenceEquiv_vertex_val {c d : MixedCode} {bt ut : ℕ} (h : c=d)
    (hc : c.Valid bt ut) (hd : d.Valid bt ut) (v : Fin c.vertices) :
    ((codeIncidenceEquiv h hc hd).vertex v).val=v.val := by subst d; rfl

theorem idxOf_product {A B : Type} (xs : List A) (ys : List B) (a : A) (b : B)
    (ha : a∈xs) (hb : b∈ys) :
    (xs ×ˢ ys).idxOf (a,b)=xs.idxOf a*ys.length+ys.idxOf b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.product_cons,List.idxOf_append]
      by_cases hx:x=a
      · subst x
        have hm:(a,b)∈ys.map (Prod.mk a):=List.mem_map.mpr ⟨b,hb,rfl⟩
        rw [if_pos hm]
        simp only [List.idxOf_cons,beq_self_eq_true,Bool.cond_true,zero_mul,zero_add]
        simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using
          idxOf_map_injective (Prod.mk a) (fun _ _ h=>congrArg Prod.snd h) ys b
      · have hm:(a,b)∉ys.map (Prod.mk x):=by
          intro h
          obtain ⟨y,_,he⟩:=List.mem_map.mp h
          exact hx (congrArg Prod.fst he)
        rw [if_neg hm,ih (List.mem_cons.mp ha |>.resolve_left (Ne.symm hx)),List.length_map]
        simp [List.idxOf_cons,Lean.Grind.beq_eq_decide_eq,hx,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end PlanarHom.FisherNumericEnumeration
