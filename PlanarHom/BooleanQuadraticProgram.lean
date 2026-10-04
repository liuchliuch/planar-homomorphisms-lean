import PlanarHom.ZeroOneVerifierPrimitives
import PlanarHom.BooleanQuadraticGauss

/-! NEW reconstruction: a concrete dense Boolean quadratic elimination program.
All loops are over materialized lists. The matrix is deliberately not required
symmetric: diagonal entries are linear terms, and opposite entries XOR. -/
namespace PlanarHom.BooleanQuadratic
open Complexity

abbrev Data := Bool × List Bool × List (List Bool)
abbrev State := Data × ℕ × Bool

def dataCode : BitEncoding Data :=
  BitEncoding.bool.prod (BitEncoding.bool.list.prod BitEncoding.bool.list.list)
def stateCode : BitEncoding State := dataCode.prod (BitEncoding.unaryNat.prod BitEncoding.bool)
def entry (q : Data) (i j : ℕ) : Bool := ((q.2.2[i]?).getD [])[j]?.getD false
def linear (q : Data) (i : ℕ) : Bool := xor (q.2.1[i]?.getD false) (entry q i i)
def cross (q : Data) (i j : ℕ) : Bool := xor (entry q i j) (entry q j i)
def dimension (q : Data) : ℕ := q.2.1.length

def keep (i j k : ℕ) : Bool := !(k==i || k==j)
def pivot (q : Data) (i j : ℕ) : Data :=
  (xor q.1 (linear q i && linear q j),
    (List.range (dimension q)).map (fun k =>
      keep i j k && xor (q.2.1[k]?.getD false)
        (xor (linear q i && cross q j k) (linear q j && cross q i k))),
    (List.range (dimension q)).map (fun k =>
      (List.range (dimension q)).map (fun l =>
        keep i j k && keep i j l &&
          xor (entry q k l) (cross q i k && cross q j l))))

def remove (q : Data) (i : ℕ) : Data :=
  (q.1,(List.range (dimension q)).map (fun k => !(k==i) && q.2.1[k]?.getD false),
    (List.range (dimension q)).map (fun k =>
      (List.range (dimension q)).map (fun l =>
        !(k==i || l==i) && entry q k l)))

def partner (q : Data) (i : ℕ) : Option ℕ :=
  (List.range (dimension q)).find? (fun j => decide (i<j) && cross q i j)

def step (s : State) (i : ℕ) : State :=
  match partner s.1 i with
  | some j => (pivot s.1 i j,s.2.1+1,s.2.2)
  | none => (remove s.1 i,s.2.1,s.2.2 || linear s.1 i)

def run (q : Data) : State := (List.range (dimension q)).foldl step (q,0,false)

def xorList (xs : List Bool) : Bool := xs.foldl xor false

def ofGraph (g : MixedCode) : Data :=
  (false,List.replicate g.vertices false,
    (List.range g.vertices).map (fun i =>
      (List.range g.vertices).map (fun j =>
        xorList (g.edges.map (fun e => (e.1==i) && (e.2.1==j))))))

def result {K : Type*} [CommRing K] (q : Data) : K :=
  let s := run q
  if s.2.2 then 0 else BooleanQuadraticGauss.sign s.1.1 * (2:K)^(dimension q-s.2.1)

def evaluate {K : Type*} [CommRing K] (g : MixedCode) : K := result (ofGraph g)

@[simp] theorem dimension_pivot (q : Data) (i j : ℕ) : dimension (pivot q i j)=dimension q := by
  simp [dimension,pivot]
@[simp] theorem dimension_remove (q : Data) (i : ℕ) : dimension (remove q i)=dimension q := by
  simp [dimension,remove]
@[simp] theorem dimension_step (s : State) (i : ℕ) : dimension (step s i).1=dimension s.1 := by
  unfold step
  split <;> simp

theorem fold_dimension (xs : List ℕ) (s : State) :
    dimension (xs.foldl step s).1=dimension s.1 := by
  induction xs generalizing s with
  | nil=>rfl
  | cons i xs ih=>simpa using (ih (step s i)).trans (dimension_step s i)

theorem fold_pairs_bound (xs : List ℕ) (s : State) :
    (xs.foldl step s).2.1 ≤ s.2.1+xs.length := by
  induction xs generalizing s with
  | nil=>simp
  | cons i xs ih=>
    have h:=ih (step s i)
    have hs : (step s i).2.1 ≤ s.2.1+1 := by
      unfold step
      split <;> simp
    simp only [List.foldl_cons,List.length_cons]
    omega

@[simp] theorem dimension_ofGraph (g : MixedCode) : dimension (ofGraph g)=g.vertices := by
  simp [dimension,ofGraph]

theorem run_pairs_bound (q : Data) : (run q).2.1≤dimension q := by
  simpa [run] using fold_pairs_bound (List.range (dimension q)) (q,0,false)

end PlanarHom.BooleanQuadratic
