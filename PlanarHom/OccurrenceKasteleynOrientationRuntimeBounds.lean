import PlanarHom.OccurrenceKasteleynOrientationStepMachines
import PlanarHom.OccurrencePfaffianStateBounds

/-! NEW reconstruction. Literal encoded bounds for every forward-loop prefix
and reverse-repair fold. Stored labels and pivots are copied from actual input
rows; no numerical label magnitude is charged as unit cost. -/
namespace PlanarHom.MultiGraph.Kasteleyn
open Complexity Polynomial

 theorem pivot_source_encoding_bound (table : List RawFace) (p : RawPivot)
    (h : ∃ ds, (p.1,ds) ∈ table ∧ ∃ a ∈ ds, a.1=p.2) :
    (pivotCode.encode p).length ≤ 3*(tableCode.encode table).length+1 := by
  obtain ⟨ds,hds,a,ha,he⟩ := h
  have hr := MaterializedFieldHeights.element_length_le_list faceCode table hds
  have hd := MaterializedFieldHeights.element_length_le_list dartCode ds ha
  have hrow : (faceCode.encode (p.1,ds)).length =
      2*(BitEncoding.nat.encode p.1).length+(dartCode.list.encode ds).length+1 :=
    BitEncoding.prod_length _ _ _
  have hda : (dartCode.encode a).length =
      2*(BitEncoding.nat.encode a.1).length+(BitEncoding.bool.encode a.2).length+1 :=
    BitEncoding.prod_length _ _ _
  simp only [pivotCode,BitEncoding.prod_length]
  change _ ≤ 3*(faceCode.list.encode table).length+1
  rw [he] at hda
  omega

 noncomputable def orientationLoopPolynomial : Polynomial ℕ :=
   C 2*X + C 2*(C 3*(C 2*X*X+X)+1) + C 3*(C 2*X*(C 3*X+1)+X)+C 3

 theorem orientation_loop_size (table : List RawFace) (i : ℕ) (hi : i ≤ table.length) :
    (orientationStateCode.encode (peelStep^[i] (initialOrientationState table))).length ≤
      orientationLoopPolynomial.eval (tableCode.encode table).length := by
  let N := (tableCode.encode table).length
  let state := peelStep^[i] (initialOrientationState table)
  have hn : table.length ≤ N := BitEncoding.list_length_le faceCode table
  have htable : state.1 = table := peelStep_iterate_table table i _ _
  have hfaces : state.2.1.Sublist (table.map Prod.fst) := peelStep_iterate_faces_sublist table i _ _
  have hlenFaces : state.2.1.length ≤ N := by
    simpa only [List.length_map] using hfaces.length_le.trans (by simpa using hn)
  have hlabel (f : ℕ) (hf : f ∈ state.2.1) : (BitEncoding.nat.encode f).length ≤ N := by
    obtain ⟨row,hrow,hf⟩ := List.mem_map.mp (hfaces.subset hf)
    have hh : (faceCode.encode row).length ≤ N :=
      MaterializedFieldHeights.element_length_le_list faceCode table hrow
    have hc := BitEncoding.prod_length BitEncoding.nat dartCode.list row
    change (faceCode.encode row).length = _ at hc
    rw [hf] at hc
    omega
  have hfcode := PfaffianList.list_encoding_bound BitEncoding.nat state.2.1 N N hlenFaces hlabel
  have hlenStack : state.2.2.length ≤ N := by
    have hh := peelStep_iterate_stack_length table i (table.map Prod.fst) []
    simp only [List.length_nil,Nat.add_zero] at hh
    exact hh.trans (hi.trans hn)
  have hpivot (p : RawPivot) (hp : p ∈ state.2.2) : (pivotCode.encode p).length ≤ 3*N+1 := by
    have hh := peelStep_iterate_stack_mem_source table i (table.map Prod.fst) [] hp
    rcases hh with hh | hh
    · simp at hh
    · exact pivot_source_encoding_bound table p hh
  have hpcode := PfaffianList.list_encoding_bound pivotCode state.2.2 N (3*N+1) hlenStack hpivot
  change (orientationStateCode.encode state).length ≤ _
  simp only [orientationStateCode,BitEncoding.prod_length]
  rw [htable]
  simp only [orientationLoopPolynomial,eval_add,eval_mul,eval_C,eval_X,eval_one]
  change 2*N+(2*(BitEncoding.nat.list.encode state.2.1).length+
    (pivotCode.list.encode state.2.2).length+1)+1 ≤ _
  dsimp only [N] at hfcode hpcode ⊢
  omega

 theorem repairState_foldl (table : List RawFace) (log : List ℕ) (ps : List RawPivot) :
    ps.foldl repairState (table,log) = (table,ps.foldl (repairLog table) log) := by
  induction ps generalizing log with
  | nil => rfl
  | cons p ps ih => simpa only [List.foldl_cons,repairState] using ih (repairLog table log p)

 theorem repair_fold_size (s : List RawFace × List ℕ) (ps : List RawPivot) (i : ℕ) :
    ((tableCode.prod logCode).encode ((ps.take i).foldl repairState s)).length ≤
      (C 20*(X+1)^2).eval (((tableCode.prod logCode).prod pivotCode.list).encode (s,ps)).length := by
  rcases s with ⟨table,log⟩
  let N := (((tableCode.prod logCode).prod pivotCode.list).encode ((table,log),ps)).length
  have hN : N = 2*(2*(tableCode.encode table).length+(logCode.encode log).length+1)+
      (pivotCode.list.encode ps).length+1 := by simp [N,BitEncoding.prod_length]
  have ht : (tableCode.encode table).length ≤ N := by omega
  have hl : (logCode.encode log).length ≤ N := by omega
  have hp : (pivotCode.list.encode ps).length ≤ N := by omega
  have hllen : log.length ≤ N := (BitEncoding.list_length_le BitEncoding.nat log).trans hl
  have hplen : ps.length ≤ N := (BitEncoding.list_length_le pivotCode ps).trans hp
  let out := (ps.take i).foldl (repairLog table) log
  have houtlen : out.length ≤ 2*N := by
    have h := repairLog_foldl_length table (ps.take i) log
    change out.length ≤ log.length+(ps.take i).length at h
    have hh : (ps.take i).length ≤ ps.length := by simp
    omega
  have helement (e : ℕ) (he : e ∈ out) : (BitEncoding.nat.encode e).length ≤ N := by
    rcases repairLog_foldl_mem table (ps.take i) log he with he | ⟨p,hp',hpe⟩
    · exact (MaterializedFieldHeights.element_length_le_list BitEncoding.nat log he).trans hl
    · have hm := List.mem_of_mem_take hp'
      have hh := (MaterializedFieldHeights.element_length_le_list pivotCode ps hm).trans hp
      have hpair := BitEncoding.prod_length BitEncoding.nat BitEncoding.nat p
      change (pivotCode.encode p).length = _ at hpair
      rw [hpe] at hpair
      omega
  have hword := PfaffianList.list_encoding_bound BitEncoding.nat out (2*N) N houtlen helement
  rw [repairState_foldl]
  change ((tableCode.prod logCode).encode (table,out)).length ≤ (C 20*(X+1)^2).eval N
  rw [BitEncoding.prod_length]
  simp only [eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one]
  change (logCode.encode out).length ≤ _ at hword
  nlinarith

end PlanarHom.MultiGraph.Kasteleyn
