import PlanarHom.PlanarityLRRotationRowMachines

namespace ReimplementedSorting
open PlanarHom.Complexity PlanarHom.ContextNatSortMachines
open PlanarHom.PlanarityLRDirect PlanarHom.PlanarityLRRawConstraints
open PlanarHom.Complexity.PairProjectionMachines PlanarHom.ArithmeticCircuitPrimitives

def direction (ascending : Bool) (a b : ℕ) : Bool := if ascending then decide (a≤b) else decide (b≤a)

 theorem fp_direction : FP (BitEncoding.bool.prod (BitEncoding.nat.prod BitEncoding.nat)) BitEncoding.bool
    (fun p=>direction p.1 p.2.1 p.2.2) := by
  have hb:=fp_fst BitEncoding.bool (BitEncoding.nat.prod BitEncoding.nat)
  have hn:=fp_snd BitEncoding.bool (BitEncoding.nat.prod BitEncoding.nat)
  have ha:=hn.comp fp_le
  have hx:=hn.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hy:=hn.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hd:=(hy.pair hx).comp fp_le
  have hp : FP (BitEncoding.bool.prod (BitEncoding.nat.prod BitEncoding.nat)) BitEncoding.bool
      (fun p=>decide (p.1=true)) := hb.congr (fun _=>by simp)
  exact hp.ite ha hd

 theorem direction_total (c : Bool) (a b : ℕ) : (direction c a b || direction c b a)=true := by
  cases c <;> simp [direction] <;> omega
 theorem direction_trans (c : Bool) (a b d : ℕ) :
    direction c a b=true→direction c b d=true→direction c a d=true := by
  cases c <;> simp [direction] <;> omega
 theorem direction_anti (c : Bool) (a b : ℕ) : direction c a b=true→direction c b a=true→a=b := by
  cases c <;> simp [direction] <;> omega

 theorem fp_context_sort : FP (BitEncoding.bool.prod BitEncoding.nat.list) BitEncoding.nat.list
    (fun p=>p.2.mergeSort (direction p.1)) :=
  fp_mergeSort BitEncoding.bool direction fp_direction direction_total direction_trans direction_anti

 theorem ascending_duplicates : sort direction true [5,1,5,0,3]=[0,1,3,5,5] := by decide
 theorem descending_duplicates : sort direction false [5,1,5,0,3]=[5,5,3,1,0] := by decide
 theorem empty_sort : sort direction true []=[] := rfl
 theorem exact_mergeSort (c : Bool) (xs : List ℕ) : sort direction c xs=xs.mergeSort (direction c) :=
  sort_eq_mergeSort direction c (direction_total c) (direction_trans c) (direction_anti c) xs

def k4 : MixedCode := ⟨4,[(0,(1,0)),(0,(2,0)),(0,(3,0)),(1,(2,0)),(1,(3,0)),(2,(3,0))],[]⟩

#eval sort direction true [5,1,5,0,3]
#eval sort direction false [5,1,5,0,3]
#eval sort direction true []
#eval sort direction true [987654321,0,987654321,2]
#eval (List.range 4).map (nestingOutgoing k4)
#eval (List.range 4).map (orderedOutgoing k4 (List.replicate 6 false))
#eval (List.range 4).map (orderedOutgoing k4 (List.replicate 6 true))

end ReimplementedSorting
