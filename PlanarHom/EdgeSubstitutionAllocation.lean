import PlanarHom.EdgeSubstitutionCode
import Mathlib.Algebra.BigOperators.Fin

/-! Literal occurrence and private-allocation bookkeeping for the numeric fold.
Positions, rather than values, index every list occurrence. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.EdgeSubstitution
open Complexity FixedGadgetNetwork

 theorem take_eq_ofFn_get {α : Type*} (l : List α) (n : ℕ) (hn : n ≤ l.length) :
    l.take n = List.ofFn (fun i : Fin n => l.get (Fin.castLE hn i)) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hn]
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_ofFn, List.get_eq_getElem, Fin.coe_castLE]

 theorem sum_take_map {α : Type*} (l : List α) (f : α → ℕ) (n : ℕ) (hn : n ≤ l.length) :
    ((l.take n).map f).sum = ∑ i : Fin n, f (l.get (Fin.castLE hn i)) := by
  rw [take_eq_ofFn_get l n hn, List.map_ofFn, List.sum_ofFn]
  rfl

 theorem getElem?_flatten_block {α : Type*} (L : List (List α))
    (i : Fin L.length) (j : Fin (L.get i).length) :
    L.flatten[(((L.take i.val).map List.length).sum + j.val)]? = some ((L.get i).get j) := by
  induction L with
  | nil => exact i.elim0
  | cons a L ih =>
    refine Fin.cases ?_ (fun k => ?_) i j
    · intro j
      simpa using (List.getElem?_append_left (l₁:=a) (l₂:=L.flatten) j.isLt).trans
        (List.getElem?_eq_getElem j.isLt)
    · intro j
      simpa only [Fin.val_succ, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.flatten_cons, Nat.add_assoc, List.getElem?_append_right (by omega : a.length ≤ a.length + (((L.take k.val).map List.length).sum + j.val)),
        Nat.add_sub_cancel_left, List.get_cons_succ] using ih k j

 def blockIndexEquiv {α : Type*} (L : List (List α)) :
    (Σ i : Fin L.length, Fin (L.get i).length) ≃ Fin L.flatten.length :=
  finSigmaFinEquiv.trans (finCongr (by
    rw [List.length_flatten]
    simpa using (sum_take_map L List.length L.length le_rfl).symm))

 @[simp] theorem blockIndexEquiv_val {α : Type*} (L : List (List α))
    (p : Σ i : Fin L.length, Fin (L.get i).length) :
    (blockIndexEquiv L p).val = (((L.take p.1.val).map List.length).sum + p.2.val) := by
  simp only [blockIndexEquiv, Equiv.trans_apply, finCongr_apply, Fin.coe_cast,
    finSigmaFinEquiv_apply, sum_take_map L List.length p.1.val p.1.isLt.le]

 @[simp] theorem get_blockIndexEquiv {α : Type*} (L : List (List α))
    (p : Σ i : Fin L.length, Fin (L.get i).length) :
    L.flatten.get (blockIndexEquiv L p) = (L.get p.1).get p.2 := by
  have h : L.flatten[(blockIndexEquiv L p).val]? = some ((L.get p.1).get p.2) := by
    simpa only [blockIndexEquiv_val] using getElem?_flatten_block L p.1 p.2
  exact (List.getElem?_eq_some_iff.mp h).choose_spec

 def ofFnBlockEquiv {α : Type*} {m : ℕ} (f : Fin m → List α) :
    (Σ i : Fin m, Fin (f i).length) ≃ Fin (List.ofFn f).flatten.length :=
   (Equiv.sigmaCongr (finCongr (List.length_ofFn (f:=f)).symm)
     (fun i => finCongr (by simp))).trans (blockIndexEquiv _)

 @[simp] theorem get_ofFnBlockEquiv {α : Type*} {m : ℕ} (f : Fin m → List α)
    (p : Σ i : Fin m, Fin (f i).length) :
    (List.ofFn f).flatten.get (ofFnBlockEquiv f p) = (f p.1).get p.2 := by
   simp only [ofFnBlockEquiv, Equiv.trans_apply, get_blockIndexEquiv]
   simp [Equiv.sigmaCongr,Equiv.sigmaCongrLeft]

 theorem get_finCongr {α : Type*} {l k : List α} (h : l = k) (i : Fin k.length) :
     l.get ((finCongr (congrArg List.length h).symm) i) = k.get i := by
   subst k
   rfl

 def gateOffset (ts : List Template) (n : ℕ) (as : List Gate) (i : ℕ) : ℕ :=
   n + ((as.take i).map (fun a => (gateTemplate ts a).privateCount)).sum

 def edgeBlocks (ts : List Template) (n : ℕ) (as : List Gate) : List (List (ℕ × ℕ × ℕ)) :=
   List.ofFn (fun i : Fin as.length =>
     (gateTemplate ts (as.get i)).edges.map
       (remapEdge (gateTemplate ts (as.get i)) (gateOffset ts n as i.val) (as.get i).2))

 theorem edgeBlocks_cons (ts : List Template) (n : ℕ) (a : Gate) (as : List Gate) :
   edgeBlocks ts n (a::as) =
     ((gateTemplate ts a).edges.map (remapEdge (gateTemplate ts a) n a.2)) ::
       edgeBlocks ts (n+(gateTemplate ts a).privateCount) as := by
   simp [edgeBlocks,List.ofFn_succ,gateOffset,Nat.add_assoc]

 theorem compile_edges (ts : List Template) (g : MixedCode) (as : List Gate) :
   (compile ts ⟨g,as⟩).edges = g.edges ++ (edgeBlocks ts g.vertices as).flatten := by
   induction as generalizing g with
   | nil => simp [compile,edgeBlocks]
   | cons a as ih =>
     change (compile ts ⟨compileStep ts g a,as⟩).edges = _
     rw [ih,edgeBlocks_cons]
     simp [compileStep,attachTemplate,List.append_assoc]

end PlanarHom.EdgeSubstitution
