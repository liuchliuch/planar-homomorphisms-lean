import PlanarHom.PlanarityDepthFirstSearchMachines
import PlanarHom.PlanarityLRConstraints

/-! NEW reconstruction. Raw occurrence and actual computed DFS queries compiled
under the unchanged ordinary graph code; no forest or alignment is supplied. -/
namespace PlanarHom.PlanarityLRRawConstraints
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

abbrev graphIndexCode := MixedCode.encoding.prod BitEncoding.nat
abbrev graphPairCode := MixedCode.encoding.prod (BitEncoding.nat.prod BitEncoding.nat)

 theorem fp_edge : FP graphIndexCode PlanarityDepthFirstSearch.edgeCode (fun p=>edge p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have hi:=fp_snd MixedCode.encoding BitEncoding.nat
  exact (((hg.comp MixedCode.fp_edges).pair hi).comp
    (PfaffianList.fp_at PlanarityDepthFirstSearch.edgeCode (0,0,0))).congr
    (fun p=>by simp [edge,PfaffianList.lookup,List.getD_eq_getElem?_getD])

 theorem fp_le : FP (BitEncoding.nat.prod BitEncoding.nat) BitEncoding.bool
    (fun p:ℕ×ℕ=>decide (p.1≤p.2)) := by
  have hs:=(fp_snd BitEncoding.nat BitEncoding.nat).pair (fp_fst BitEncoding.nat BitEncoding.nat)
  exact ((hs.comp BinaryArithmetic.fp_comparison).comp (fp_bool_unary BitEncoding.bool Bool.not)).congr
    (fun p=>by
      simp only [Function.comp_apply]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq]
      omega)

 theorem fp_lower : FP graphIndexCode BitEncoding.nat (fun p=>lower p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have hl:=fp_edge.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hr:=(fp_edge.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)
  have hdl:=(hg.pair hl).comp PlanarityDepthFirstSearch.fp_height
  have hdr:=(hg.pair hr).comp PlanarityDepthFirstSearch.fp_height
  exact ((hdl.pair hdr).comp fp_le).ite hl hr

 theorem fp_upper : FP graphIndexCode BitEncoding.nat (fun p=>upper p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have hl:=fp_edge.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hr:=(fp_edge.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)
  have hdl:=(hg.pair hl).comp PlanarityDepthFirstSearch.fp_height
  have hdr:=(hg.pair hr).comp PlanarityDepthFirstSearch.fp_height
  exact ((hdl.pair hdr).comp fp_le).ite hr hl

 theorem fp_isTree : FP graphIndexCode BitEncoding.bool (fun p=>isTree p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have he:=fp_snd MixedCode.encoding BitEncoding.nat
  have hm:=(hg.comp MixedCode.fp_edges).comp (ListCodecMachines.fp_length PlanarityDepthFirstSearch.edgeCode)
  have hvalid:=(he.pair hm).comp BinaryArithmetic.fp_comparison
  have hgu:=hg.pair fp_upper
  have hh:=hgu.comp PlanarityDepthFirstSearch.fp_height
  have hpos:=((fp_const graphIndexCode BitEncoding.nat 0).pair hh).comp BinaryArithmetic.fp_comparison
  have hp:=hgu.comp PlanarityDepthFirstSearch.fp_parentEdge
  have heq:=(hp.pair he).comp PfaffianList.fp_nat_eq
  have hand:=(hpos.pair heq).comp (fp_bool_gate (fun p=>p.1 && p.2))
  exact ((hvalid.pair hand).comp (fp_bool_gate (fun p=>p.1 && p.2))).congr (fun p=>by simp [isTree])

 theorem fp_source : FP graphIndexCode BitEncoding.nat (fun p=>source p.1 p.2) := by
  have ht : FP graphIndexCode BitEncoding.bool (fun p=>decide (isTree p.1 p.2=true)) :=
    fp_isTree.congr (fun _=>by simp)
  exact ht.ite fp_lower fp_upper

 theorem fp_target : FP graphIndexCode BitEncoding.nat (fun p=>target p.1 p.2) := by
  have ht : FP graphIndexCode BitEncoding.bool (fun p=>decide (isTree p.1 p.2=true)) :=
    fp_isTree.congr (fun _=>by simp)
  exact ht.ite fp_upper fp_lower

 theorem fp_isBack : FP graphIndexCode BitEncoding.bool (fun p=>isBack p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have he:=fp_snd MixedCode.encoding BitEncoding.nat
  have hm:=(hg.comp MixedCode.fp_edges).comp (ListCodecMachines.fp_length PlanarityDepthFirstSearch.edgeCode)
  have hv:=(he.pair hm).comp BinaryArithmetic.fp_comparison
  have hn:=fp_isTree.comp (fp_bool_unary BitEncoding.bool Bool.not)
  have hne:=((fp_source.pair fp_target).comp PfaffianList.fp_nat_eq).comp
    (fp_bool_unary BitEncoding.bool Bool.not)
  have hb:=(hn.pair hne).comp (fp_bool_gate (fun p=>p.1 && p.2))
  exact ((hv.pair hb).comp (fp_bool_gate (fun p=>p.1 && p.2))).congr (fun p=>by simp [isBack])

 theorem fp_targetHeight : FP graphIndexCode BitEncoding.nat (fun p=>targetHeight p.1 p.2) :=
  ((fp_fst MixedCode.encoding BitEncoding.nat).pair fp_target).comp PlanarityDepthFirstSearch.fp_height

 theorem fp_ancestor : FP graphPairCode BitEncoding.bool (fun p=>ancestor p.1 p.2.1 p.2.2) := by
  have heq:=(fp_snd MixedCode.encoding (BitEncoding.nat.prod BitEncoding.nat)).comp PfaffianList.fp_nat_eq
  exact ((heq.pair PlanarityDepthFirstSearch.fp_isAncestor).comp
    (fp_bool_gate (fun p=>p.1 || p.2))).congr (fun p=>by simp [ancestor])

 theorem fp_edgeRange : FP MixedCode.encoding BitEncoding.nat.list (fun g=>List.range g.edges.length) :=
  (MixedCode.fp_edges.comp (ListUnaryLengthMachine.fp_length PlanarityDepthFirstSearch.edgeCode)).comp
    UnaryArithmeticMachines.fp_range

 theorem fp_min : FP (BitEncoding.nat.prod BitEncoding.nat) BitEncoding.nat (fun p:ℕ×ℕ=>min p.1 p.2) :=
  (fp_le.ite (fp_fst BitEncoding.nat BitEncoding.nat) (fp_snd BitEncoding.nat BitEncoding.nat)).congr
    (fun p=>by split_ifs with h <;> simp [min_def,h])

 theorem fold_min_le (xs : List ℕ) (a : ℕ) : xs.foldl min a≤a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => exact (ih (min a x)).trans (min_le_left _ _)

 theorem fp_foldMin : FP (BitEncoding.nat.prod BitEncoding.nat.list) BitEncoding.nat
    (fun p:ℕ×List ℕ=>p.2.foldl min p.1) := by
  apply ListFoldMachines.fp_foldl BitEncoding.nat BitEncoding.nat min fp_min Polynomial.X
  intro a xs i hi
  have hh:=Nat.size_le_size (fold_min_le (xs.take i) a)
  have hl : (BitEncoding.nat.encode ((xs.take i).foldl min a)).length≤(BitEncoding.nat.encode a).length := by
    simpa only [BitEncoding.nat,BinaryArithmetic.encodeNat_length] using hh
  simp only [Polynomial.eval_X,BitEncoding.prod_length]
  omega

end PlanarHom.PlanarityLRRawConstraints
