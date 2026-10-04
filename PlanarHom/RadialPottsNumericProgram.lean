import PlanarHom.RadialPottsNumericVertices
import PlanarHom.MixedPlanarCode

/-! A materialized radial graph program. Runtime m and k are unary dimensions;
inverse rotation entries and every emitted endpoint are binary naturals. This
module defines the total program, without imposing an external rotation promise. -/
namespace PlanarHom.RadialPotts.Numeric
open Complexity

abbrev Input := ℕ × (ℕ × List ℕ)
def inputEncoding : BitEncoding Input :=
  BitEncoding.unaryNat.prod (BitEncoding.unaryNat.prod BitEncoding.nat.list)

 def whiteName (k e r i : ℕ) : ℕ := (4*k^2)*e+4*r^2+i

 def switchedName (k e r i : ℕ) : ℕ :=
  if i=0 ∧ r+1<k then whiteName k e (r+1) 1
  else if i=1 ∧ 0<r then whiteName k e (r-1) 0 else whiteName k e r i

 def portName (p : Input) (e s a : ℕ) : ℕ :=
  p.1*(4*p.2.1^2)+p.2.1*(if s%2=1 then 2*e+s/2 else p.2.2.getD (2*e+s/2) 0)+
    (if s%2=1 then a else p.2.1-1-a)

 def longEntry (p : Input) (e r s a : ℕ) : ℕ × (ℕ × ℕ) :=
  (whiteName p.2.1 e r (s*(2*r+1)+2*a),
    (if r+1<p.2.1 then whiteName p.2.1 e (r+1) (s*(2*(r+1)+1)+2*a+1)
     else portName p e s a,0))

 def shortEntry (k e r j : ℕ) (blue : Bool) : ℕ × (ℕ × ℕ) :=
  if blue then (whiteName k e r (2*j+1),(whiteName k e r ((2*j+2)%(8*r+4)),1))
  else (switchedName k e r (2*j),(switchedName k e r (2*j+1),1))

 def ringEntries (p : Input) (e r : ℕ) : List (ℕ × (ℕ × ℕ)) :=
  (List.range 4).flatMap (fun s => (List.range (r+1)).map (longEntry p e r s)) ++
    (List.range (4*r+2)).flatMap (fun j => [shortEntry p.2.1 e r j false,shortEntry p.2.1 e r j true])

 def edgeEntries (p : Input) : List (ℕ × (ℕ × ℕ)) :=
  (List.range p.1).flatMap (fun e => (List.range p.2.1).flatMap (ringEntries p e))

 def output (p : Input) : MixedCode :=
  ⟨Assembly.vertexCount p.1 p.2.1,edgeEntries p,[]⟩

 theorem ringEntries_length (p : Input) (e r : ℕ) :
    (ringEntries p e r).length=4*(r+1)+2*(4*r+2) := by
  simp [ringEntries,List.length_flatMap,mul_comm]
  ring

 theorem edgeEntries_length (p : Input) :
    (edgeEntries p).length=p.1*(6*p.2.1^2+2*p.2.1) := by
  have hr : ∀ k e,((List.range k).flatMap (ringEntries p e)).length=6*k^2+2*k := by
    intro k e
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ,List.flatMap_append,List.length_append]
      simp only [List.flatMap_singleton,ih,ringEntries_length]
      ring
  simp [edgeEntries,List.length_flatMap,hr]
end PlanarHom.RadialPotts.Numeric
