import PlanarHom.ReplicationPlanarity
import PlanarHom.FisherNumericRotationTransport

/-! NEW literal e*t+r occurrence numbering for homogeneous parallel copies.
The incidence equivalence follows the actual emitted flatMap/replicate list;
it does not choose an arbitrary cardinality bijection. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.UniformParallelCode
open Complexity MultiGraph

theorem uniform_length {A : Type} (xs : List A) (t : ℕ) :
    (xs.flatMap (fun x=>List.replicate t x)).length=xs.length*t := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons,List.length_append,List.length_replicate,ih,List.length_cons,Nat.add_mul,Nat.one_mul]; omega

theorem uniform_get {A : Type} (xs : List A) (t i j : ℕ) (hi : i<xs.length) (hj : j<t) :
    (xs.flatMap (fun x=>List.replicate t x))[i*t+j]'(by rw [uniform_length]; nlinarith)=xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.flatMap_cons,List.getElem_cons_zero]
      rw [List.getElem_append_left (by simpa using hj)]
      simp
    | succ i =>
      have hi' : i<xs.length := by simpa using hi
      simp only [List.flatMap_cons,List.getElem_cons_succ]
      rw [List.getElem_append_right (by simp only [List.length_replicate]; nlinarith)]
      simp only [List.length_replicate]
      have he : (i+1)*t+j-t=i*t+j := by simp only [Nat.add_mul,Nat.one_mul]; omega
      simpa only [he] using ih i hi'

def validParallel (g : MixedCode) (hg : g.Valid 1 0) (t : ℕ) : (g.parallelLabel 0 t).Valid 1 0 :=
  g.parallelLabel_valid 0 t 1 0 hg

theorem edges_eq (g : MixedCode) (hg : g.Valid 1 0) (t : ℕ) :
    (g.parallelLabel 0 t).edges=g.edges.flatMap (fun e=>List.replicate t e) := by
  rw [g.parallelLabel_edges_eq]
  rw [List.flatMap_def,List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro e he
  have hz : e.2.2=0 := by have hh:=(hg.1 e he).2.2; omega
  simp [MixedCode.selectedCount,hz]

theorem edge_length (g : MixedCode) (hg : g.Valid 1 0) (t : ℕ) :
    (g.parallelLabel 0 t).edges.length=g.edges.length*t := by rw [edges_eq g hg,uniform_length]

def edgeEquiv (g : MixedCode) (hg : g.Valid 1 0) (t : ℕ) :
    (Fin g.edges.length×Fin t)≃Fin (g.parallelLabel 0 t).edges.length :=
  finProdFinEquiv.trans (finCongr (edge_length g hg t).symm)

@[simp] theorem edgeEquiv_val (g : MixedCode) (hg : g.Valid 1 0) (t : ℕ)
    (e : Fin g.edges.length) (r : Fin t) :
    (edgeEquiv g hg t (e,r)).val=e.val*t+r.val := by
  simp [edgeEquiv,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

theorem edge_get (g : MixedCode) (hg : g.Valid 1 0) (t : ℕ)
    (e : Fin g.edges.length) (r : Fin t) :
    (g.parallelLabel 0 t).edges.get (edgeEquiv g hg t (e,r))=g.edges.get e := by
  have h := uniform_get g.edges t e.val r.val e.isLt r.isLt
  have hs := congrArg (fun xs : List (ℕ×(ℕ×ℕ))=>xs[e.val*t+r.val]?) (edges_eq g hg t)
  have hi : e.val*t+r.val<(g.parallelLabel 0 t).edges.length := by rw [edge_length g hg t]; nlinarith [e.isLt,r.isLt]
  have hj : e.val*t+r.val<(g.edges.flatMap (fun x=>List.replicate t x)).length := by rw [uniform_length]; nlinarith [e.isLt,r.isLt]
  simp only [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] at hs
  simpa only [List.get_eq_getElem,edgeEquiv_val] using (Option.some.inj hs).trans h

def incidence (g : MixedCode) (hg : g.Valid 1 0) (t : ℕ) :
    IncidenceEquiv ((g.toMultiGraph hg).thicken t)
      ((g.parallelLabel 0 t).toMultiGraph (validParallel g hg t)) where
  vertex:=Equiv.refl _
  edge:=edgeEquiv g hg t
  src_eq p:=by
    apply Fin.ext
    exact congrArg (fun e : ℕ×(ℕ×ℕ)=>e.1) (edge_get g hg t p.1 p.2)
  dst_eq p:=by
    apply Fin.ext
    exact congrArg (fun e : ℕ×(ℕ×ℕ)=>e.2.1) (edge_get g hg t p.1 p.2)

end PlanarHom.UniformParallelCode
