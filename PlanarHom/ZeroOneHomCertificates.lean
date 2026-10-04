import PlanarHom.TotalGraphCodecParsers
import PlanarHom.PlanarGraphCode
import PlanarHom.SharpPBridge
import Mathlib.Logic.Equiv.Fin.Basic

/-! NEW fixed-relation graph-homomorphism certificates. Each vertex receives
one canonical one-hot color word; every remaining witness bit is forced false.
This includes the empty color set, empty graph, loops and parallel occurrences. -/
noncomputable section
open Classical
namespace PlanarHom.ZeroOneSharpPMembership
open Complexity
abbrev Relation (q:ℕ) := Fin q→Fin q→Bool

def IsHom (q:ℕ) (R:Relation q) (g:GraphCode) (hg:g.Valid) (c:Fin g.vertices→Fin q) : Prop :=
  ∀e:Fin g.edges.length,R (c ((g.toMultiGraph hg).src e)) (c ((g.toMultiGraph hg).dst e))=true
abbrev Hom (q:ℕ) (R:Relation q) (g:GraphCode) (hg:g.Valid) :=
  {c:Fin g.vertices→Fin q // IsHom q R g hg c}
def count (q:ℕ) (R:Relation q) (g:GraphCode) (hg:g.Valid) : ℕ := Fintype.card (Hom q R g hg)

def getBit (w:Bits) (k:ℕ) : Bool := w[k]?.getD false

def Matches (q:ℕ) (w:Bits) (v:ℕ) (c:Fin q) : Prop :=
  ∀j:Fin q,getBit w (q*v+j.val)=decide (c=j)

def rowMatch (q:ℕ) (w:Bits) (v:ℕ) (c:Fin q) : Bool := decide (Matches q w v c)
def vertexCheck (q:ℕ) (w:Bits) (v:ℕ) : Bool := decide (∃c:Fin q,Matches q w v c)
def edgeCheck (q:ℕ) (R:Relation q) (w:Bits) (e:ℕ×ℕ) : Bool :=
  decide (∃c d:Fin q,Matches q w e.1 c ∧ Matches q w e.2 d ∧ R c d=true)
def padding (n q:ℕ) (w:Bits) : Bool :=
  (List.range w.length).all (fun k=>if k<n*q then true else !(getBit w k))
def verifyGraph (q:ℕ) (R:Relation q) (g:GraphCode) (w:Bits) : Bool :=
  decide g.Valid && (List.range g.vertices).all (vertexCheck q w) &&
    g.edges.all (edgeCheck q R w) && padding g.vertices q w

theorem matches_unique {q:ℕ} {w:Bits} {v:ℕ} {c d:Fin q}
    (hc:Matches q w v c) (hd:Matches q w v d) : c=d := by
  have h:=hc c
  have hh:=hd c
  simp only [decide_true] at h
  rw [h] at hh
  exact (of_decide_eq_true hh.symm).symm

theorem padding_true (n q:ℕ) (w:Bits) : padding n q w=true ↔
    ∀k,k<w.length → n*q≤k → getBit w k=false := by
  simp only [padding,List.all_eq_true,List.mem_range]
  constructor
  · intro h k hk hge
    have hh:=h k hk
    simpa [Nat.not_lt.mpr hge] using hh
  · intro h k hk
    by_cases hl:k<n*q
    · simp [hl]
    · simp [hl,h k hk (by omega)]

theorem verifyGraph_true (q:ℕ) (R:Relation q) (g:GraphCode) (w:Bits) :
    verifyGraph q R g w=true ↔ g.Valid ∧
      (∀v,v<g.vertices → ∃c:Fin q,Matches q w v c) ∧
      (∀e∈g.edges,∃c d:Fin q,Matches q w e.1 c ∧ Matches q w e.2 d ∧ R c d=true) ∧
      (∀k,k<w.length → g.vertices*q≤k → getBit w k=false) := by
  simp only [verifyGraph,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range,
    vertexCheck,edgeCheck,padding_true,and_assoc]

def oneHotWord {n q:ℕ} (c:Fin n→Fin q) (k:Fin (n*q)) : Bool :=
  let p:=finProdFinEquiv.symm k
  decide (c p.1=p.2)

def paddedWord {n q:ℕ} (c:Fin n→Fin q) (L:ℕ) (k:Fin (L*q)) : Bool :=
  if h:k.val<n*q then oneHotWord c ⟨k.val,h⟩ else false

theorem getBit_ofFn {N:ℕ} (w:Fin N→Bool) (k:ℕ) (hk:k<N) :
    getBit (List.ofFn w) k=w ⟨k,hk⟩ := by simp [getBit,List.getElem?_ofFn,hk]

theorem paddedWord_matches {n q L:ℕ} (c:Fin n→Fin q) (hL:n≤L) (v:Fin n) :
    Matches q (List.ofFn (paddedWord c L)) v.val (c v) := by
  intro j
  have hsmall:q*v.val+j.val<n*q := by
    have h:=(finProdFinEquiv (v,j)).isLt
    change j.val+q*v.val<n*q at h
    omega
  have hbig:q*v.val+j.val<L*q := lt_of_lt_of_le hsmall (Nat.mul_le_mul_right q hL)
  rw [getBit_ofFn _ _ hbig]
  simp only [paddedWord,dif_pos hsmall]
  have hk:(⟨q*v.val+j.val,hsmall⟩:Fin (n*q))=finProdFinEquiv (v,j) := by
    apply Fin.ext
    simp only [finProdFinEquiv,Equiv.coe_fn_mk]
    omega
  rw [hk]
  simp only [oneHotWord,Equiv.symm_apply_apply]

theorem paddedWord_padding {n q L:ℕ} (c:Fin n→Fin q) :
    padding n q (List.ofFn (paddedWord c L))=true := by
  apply (padding_true _ _ _).mpr
  intro k hk hge
  have hlt:k<L*q := by simpa using hk
  rw [getBit_ofFn _ _ hlt]
  simp [paddedWord,Nat.not_lt.mpr hge]

end PlanarHom.ZeroOneSharpPMembership
