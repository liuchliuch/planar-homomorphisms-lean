import PlanarHom.GraphComponentCode
import PlanarHom.ListContextFilterMachines
import PlanarHom.ListPredicateMachines
import PlanarHom.ListReverseMachines
import PlanarHom.ListUnaryLengthMachine
import PlanarHom.NatListSumMachines
import PlanarHom.UnaryRangeMachines
import PlanarHom.MixedUnaryParallelMachines
import PlanarHom.GraphCodeNormalization
import PlanarHom.RationalCircuits

/-! Actual TM2 programs for the component partition, stable local extraction,
and raw accepted-word extension. All growing folds carry explicit code-size
bounds; no graph operation is postulated polynomial-time. -/
namespace PlanarHom.GraphComponentMachines
open Complexity GraphComponentCode PairProjectionMachines ArithmeticCircuitPrimitives
open ListFlattenMachines Polynomial

abbrev natCode := BitEncoding.nat
abbrev edgeCode := natCode.prod (natCode.prod natCode)
abbrev partsCode := natCode.list.list

/-- Right-to-left index search state. The left coordinate is the fixed key. -/
def indexStep (s : ℕ × ℕ) (a : ℕ) : ℕ × ℕ :=
  (s.1, if a = s.1 then 0 else s.2 + 1)

theorem fp_indexStep : FP ((natCode.prod natCode).prod natCode)
    (natCode.prod natCode) (fun p => indexStep p.1 p.2) := by
  have hs := fp_fst (natCode.prod natCode) natCode
  have hv := hs.comp (fp_fst natCode natCode)
  have hn := hs.comp (fp_snd natCode natCode)
  have ha := fp_snd (natCode.prod natCode) natCode
  have ht := (ha.pair hv).comp NatListSumMachines.fp_equal
  have hincr := (hn.pair (fp_const _ natCode 1)).comp BinaryArithmetic.fp_addition
  exact hv.pair (ht.ite (fp_const _ natCode 0) hincr)

private theorem nat_succ_length (a : ℕ) :
    (natCode.encode (a+1)).length ≤ (natCode.encode a).length+2 := by
  have h := BinaryArithmetic.addBits_length_le false (Computability.encodeNat a) (Computability.encodeNat 1)
  rw [BinaryArithmetic.addBits_encodeNat] at h
  have ho : (Computability.encodeNat 1).length = 1 := by simp [BinaryArithmetic.encodeNat_length]
  simpa only [natCode,BitEncoding.nat,ho,Nat.add_assoc] using h

private theorem indexStep_length (s : ℕ × ℕ) (a : ℕ) :
    ((natCode.prod natCode).encode (indexStep s a)).length ≤
      ((natCode.prod natCode).encode s).length+2 := by
  have hn := nat_succ_length s.2
  simp only [indexStep,BitEncoding.prod_length]
  split
  · have hz : (natCode.encode 0).length = 0 := by simp [natCode,BitEncoding.nat,BinaryArithmetic.encodeNat_length]
    rw [hz]
    omega
  · omega

private theorem indexFold_length (s : ℕ × ℕ) (xs : List ℕ) :
    ((natCode.prod natCode).encode (xs.foldl indexStep s)).length ≤
      ((natCode.prod natCode).encode s).length+2*xs.length := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih =>
    have h := ih (indexStep s a)
    have hs := indexStep_length s a
    simp only [List.foldl_cons,List.length_cons]
    omega

private theorem indexFold_bound (s : ℕ × ℕ) (xs : List ℕ) (i : ℕ) :
    ((natCode.prod natCode).encode ((xs.take i).foldl indexStep s)).length ≤
      (C 3*X).eval (((natCode.prod natCode).prod natCode.list).encode (s,xs)).length := by
  have h := indexFold_length s (xs.take i)
  have hx := BitEncoding.list_length_le natCode xs
  have ht : (xs.take i).length ≤ xs.length := by simp
  have hN : (((natCode.prod natCode).prod natCode.list).encode (s,xs)).length =
    2*((natCode.prod natCode).encode s).length+(natCode.list.encode xs).length+1 :=
    BitEncoding.prod_length _ _ _
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  omega

theorem indexFold_reverse (v : ℕ) (xs : List ℕ) :
    xs.reverse.foldl indexStep (v,0) = (v,xs.idxOf v) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih,indexStep,List.idxOf_cons]
    by_cases h : a=v <;> simp [h,Bool.beq_eq_decide_eq]

/-- Dynamic first-index lookup, including the exact out-of-list length default. -/
theorem fp_index : FP (natCode.prod natCode.list) natCode (fun p => p.2.idxOf p.1) := by
  have hf := ListFoldMachines.fp_foldl natCode (natCode.prod natCode) indexStep fp_indexStep
    (C 3*X) (fun s xs i _ => indexFold_bound s xs i)
  have hv := fp_fst natCode natCode.list
  have hx := (fp_snd natCode natCode.list).comp (ListReverseMachines.fp_reverse natCode)
  have hs := hv.pair (fp_const (natCode.prod natCode.list) natCode 0)
  exact (((hs.pair hx).comp hf).comp (fp_snd natCode natCode)).congr
    (fun p => congrArg Prod.snd (indexFold_reverse p.1 p.2))

theorem fp_mem : FP (natCode.prod natCode.list) BitEncoding.bool (fun p => decide (p.1 ∈ p.2)) := by
  exact (ListPredicateMachines.fp_member natCode (fun p => decide (p.1=p.2))
    NatListSumMachines.fp_equal).congr (fun p => by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true,decide_eq_true_eq]
      simp [eq_comm])

theorem fp_touches : FP (edgeCode.prod natCode.list) BitEncoding.bool (fun p => touches p.1 p.2) := by
  have he := fp_fst edgeCode natCode.list
  have hx := fp_snd edgeCode natCode.list
  have hu := he.comp (fp_fst natCode (natCode.prod natCode))
  have hv := (he.comp (fp_snd natCode (natCode.prod natCode))).comp (fp_fst natCode natCode)
  have hm₁ := (hu.pair hx).comp fp_mem
  have hm₂ := (hv.pair hx).comp fp_mem
  exact ((hm₁.pair hm₂).comp (fp_bool_gate (fun p => p.1 || p.2))).congr
    (fun p => by simp [touches])

theorem fp_merge : FP (partsCode.prod edgeCode) partsCode (fun p => merge p.1 p.2) := by
  have hp := fp_fst partsCode edgeCode
  have he := fp_snd partsCode edgeCode
  have hswap := he.pair hp
  have hselected := hswap.comp (ListContextFilterMachines.fp_filterWithContext
    edgeCode natCode.list (fun p => touches p.1 p.2) fp_touches)
  have hnot := fp_touches.comp (fp_bool_unary BitEncoding.bool not)
  have hremaining := hswap.comp (ListContextFilterMachines.fp_filterWithContext
    edgeCode natCode.list (fun p => !(touches p.1 p.2)) hnot)
  exact ((hselected.comp (fp_flatten natCode)).pair hremaining).comp
    (ListMutationMachines.fp_cons natCode.list)

/-- Merging preserves the precise multiset of original vertex occurrences. -/
theorem merge_flatten_perm (ps : Parts) (e : Edge) : (merge ps e).flatten.Perm ps.flatten := by
  simpa [merge,List.flatten_append] using (List.filter_append_perm (touches e) ps).flatten

def mass (ps : Parts) : ℕ := payloadSize natCode ps.flatten

private theorem mass_eq_sum (ps : Parts) : mass ps = (ps.map (payloadSize natCode)).sum := by
  induction ps with
  | nil => simp [mass,payloadSize,BitEncoding.frames]
  | cons xs ps ih => simpa [mass,payloadSize_append] using congrArg (fun n => payloadSize natCode xs+n) ih

private theorem mass_merge (ps : Parts) (e : Edge) : mass (merge ps e) = mass ps := by
  have hp := merge_flatten_perm ps e
  have hs := (hp.map (fun a => (natCode.encode a).length)).sum_eq
  simp only [mass,payloadSize_eq,hp.length_eq,hs]

private theorem mass_fold (ps : Parts) (es : List Edge) : mass (es.foldl merge ps) = mass ps := by
  induction es generalizing ps with
  | nil => rfl
  | cons e es ih => simpa only [List.foldl_cons,ih] using mass_merge ps e

private theorem merge_length (ps : Parts) (e : Edge) : (merge ps e).length ≤ ps.length+1 := by
  simp only [merge,List.length_cons]
  have h := List.length_filter_le (fun xs => !(touches e xs)) ps
  omega

private theorem fold_length (ps : Parts) (es : List Edge) :
    (es.foldl merge ps).length ≤ ps.length+es.length := by
  induction es generalizing ps with
  | nil => simp
  | cons e es ih =>
    have h := ih (merge ps e)
    have hm := merge_length ps e
    simp only [List.foldl_cons,List.length_cons]
    omega

private theorem parts_length_le (ps : Parts) :
    (partsCode.encode ps).length ≤ 18*mass ps+9*ps.length+1 := by
  have h := word_length_le_payload natCode.list ps
  have hs := List.sum_le_sum (fun xs (_ : xs∈ps) => word_length_le_payload natCode xs)
  rw [payloadSize_eq] at h
  change (natCode.list.list.encode ps).length ≤ _
  rw [mass_eq_sum]
  simp only [List.sum_map_add,List.sum_map_mul_left,List.map_const',List.sum_replicate,
    Nat.nsmul_eq_mul,mul_one] at hs
  omega

private theorem mass_le_word (ps : Parts) : mass ps ≤ (partsCode.encode ps).length := by
  have h := payloadSize_le_word natCode.list ps
  have hs := List.sum_le_sum (fun xs (_ : xs∈ps) => payloadSize_le_word natCode xs)
  rw [payloadSize_eq] at h
  change mass ps ≤ (natCode.list.list.encode ps).length
  rw [mass_eq_sum]
  omega

/-- Every intermediate partition has linear bit size in the initial parts and
edge list. No endpoint-validity premise is used, including malformed indices. -/
theorem mergeFold_bound (ps : Parts) (es : List Edge) (i : ℕ) :
    (partsCode.encode ((es.take i).foldl merge ps)).length ≤
      (C 40*X+1).eval ((partsCode.prod edgeCode.list).encode (ps,es)).length := by
  let N := ((partsCode.prod edgeCode.list).encode (ps,es)).length
  have hN : N = 2*(partsCode.encode ps).length+(edgeCode.list.encode es).length+1 :=
    BitEncoding.prod_length _ _ _
  have hps : ps.length ≤ (partsCode.encode ps).length := BitEncoding.list_length_le natCode.list ps
  have hes := BitEncoding.list_length_le edgeCode es
  have hm := mass_le_word ps
  have hl := fold_length ps (es.take i)
  have ht : (es.take i).length ≤ es.length := by simp
  have hcode := parts_length_le ((es.take i).foldl merge ps)
  rw [mass_fold] at hcode
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ 40*N+1
  omega

theorem fp_mergeFold : FP (partsCode.prod edgeCode.list) partsCode (fun p => p.2.foldl merge p.1) :=
  ListFoldMachines.fp_foldl edgeCode partsCode merge fp_merge (C 40*X+1)
    (fun ps es i _ => mergeFold_bound ps es i)

theorem fp_initial : FP BitEncoding.unaryNat partsCode initial := by
  have hsingleton : FP natCode natCode.list (fun n => [n]) :=
    ((fp_id natCode).pair (fp_const natCode natCode.list [])).comp (ListMutationMachines.fp_cons natCode)
  exact UnaryRangeMachines.fp_range.comp (ListMapMachines.fp_map natCode natCode.list _ hsingleton)

theorem fp_nonempty : FP natCode.list BitEncoding.bool (fun xs => !xs.isEmpty) := by
  have h := (ListCodecMachines.fp_length natCode).comp RationalCircuits.fp_nat_isZero
  exact (h.comp (fp_bool_unary BitEncoding.bool not)).congr (fun xs => by cases xs <;> simp)

theorem fp_parts : FP MixedCode.encoding partsCode parts := by
  have hi := MixedCode.fp_vertices.comp fp_initial
  have hf := (hi.pair MixedCode.fp_edges).comp fp_mergeFold
  exact hf.comp (ListFilterMachines.fp_filter natCode.list _ fp_nonempty)

theorem fp_edgeInside : FP (natCode.list.prod edgeCode) BitEncoding.bool (fun p => edgeInside p.1 p.2) := by
  have hx := fp_fst natCode.list edgeCode
  have he := fp_snd natCode.list edgeCode
  have hu := he.comp (fp_fst natCode (natCode.prod natCode))
  have hv := (he.comp (fp_snd natCode (natCode.prod natCode))).comp (fp_fst natCode natCode)
  have hm₁ := (hu.pair hx).comp fp_mem
  have hm₂ := (hv.pair hx).comp fp_mem
  exact ((hm₁.pair hm₂).comp (fp_bool_gate (fun p => p.1 && p.2))).congr
    (fun p => by simp [edgeInside])

theorem fp_reindexEdge : FP (natCode.list.prod edgeCode) edgeCode
    (fun p => (p.1.idxOf p.2.1,p.1.idxOf p.2.2.1,p.2.2.2)) := by
  have hx := fp_fst natCode.list edgeCode
  have he := fp_snd natCode.list edgeCode
  have hu := he.comp (fp_fst natCode (natCode.prod natCode))
  have het := he.comp (fp_snd natCode (natCode.prod natCode))
  have hv := het.comp (fp_fst natCode natCode)
  have hl := het.comp (fp_snd natCode natCode)
  exact ((hu.pair hx).comp fp_index).pair (((hv.pair hx).comp fp_index).pair hl)

theorem fp_unaryInside : FP (natCode.list.prod (natCode.prod natCode)) BitEncoding.bool
    (fun p => decide (p.2.1 ∈ p.1)) := by
  have hx := fp_fst natCode.list (natCode.prod natCode)
  have hu := (fp_snd natCode.list (natCode.prod natCode)).comp (fp_fst natCode natCode)
  exact (hu.pair hx).comp fp_mem

theorem fp_reindexUnary : FP (natCode.list.prod (natCode.prod natCode)) (natCode.prod natCode)
    (fun p => (p.1.idxOf p.2.1,p.2.2)) := by
  have hx := fp_fst natCode.list (natCode.prod natCode)
  have hu := fp_snd natCode.list (natCode.prod natCode)
  have hv := hu.comp (fp_fst natCode natCode)
  have hl := hu.comp (fp_snd natCode natCode)
  exact ((hv.pair hx).comp fp_index).pair hl

/-- Both stable filters and every endpoint lookup execute on the exact original
occurrence codec. The vertex count is emitted in unary. -/
theorem fp_extract : FP (MixedCode.encoding.prod natCode.list) MixedCode.encoding
    (fun p => extract p.1 p.2) := by
  have hg := fp_fst MixedCode.encoding natCode.list
  have hx := fp_snd MixedCode.encoding natCode.list
  have hn := hx.comp (ListUnaryLengthMachine.fp_length natCode)
  have hes := (hx.pair (hg.comp MixedCode.fp_edges)).comp
    (ListContextFilterMachines.fp_filterWithContext natCode.list edgeCode _ fp_edgeInside)
  have he := (hx.pair hes).comp
    (ListContextMachines.fp_mapWithContext natCode.list edgeCode edgeCode _ fp_reindexEdge)
  have hus := (hx.pair (hg.comp MixedCode.fp_unaries)).comp
    (ListContextFilterMachines.fp_filterWithContext natCode.list (natCode.prod natCode) _ fp_unaryInside)
  have hu := (hx.pair hus).comp
    (ListContextMachines.fp_mapWithContext natCode.list (natCode.prod natCode)
      (natCode.prod natCode) _ fp_reindexUnary)
  exact (hn.pair (he.pair hu)).transportOutput (fun _ => rfl)

/-- The actual connected-component program, on canonical mixed occurrence codes.
Its machine handles arbitrary endpoint and label words without an FP premise. -/
theorem fp_components : FP MixedCode.encoding MixedCode.encoding.list components :=
  ((fp_id MixedCode.encoding).pair fp_parts).comp
    (ListContextMachines.fp_mapWithContext MixedCode.encoding natCode.list MixedCode.encoding _ fp_extract)

noncomputable def componentsComputer :
    Turing.TM2ComputableInPolyTime MixedCode.encoding.toFinEncoding
      MixedCode.encoding.list.toFinEncoding components := Classical.choice fp_components

/-- Normalize every accepted raw field/header, then run the same concrete
component machine. Runtime is charged against the actual original raw length. -/
noncomputable def componentsRawComputer :
    Turing.TM2ComputableInPolyTime
      (BitEncoding.ValidWord.encoding MixedCode.encoding).toFinEncoding
      MixedCode.encoding.list.toFinEncoding (fun w => components w.value) :=
  MachineComposition.composeComputers MixedCode.normalizer componentsComputer

noncomputable def components_raw_outputs (raw : Bits) (g : MixedCode)
    (hd : MixedCode.encoding.decode raw = some g) :
    Turing.TM2OutputsInTime componentsRawComputer.tm
      (raw.map componentsRawComputer.inputAlphabet.symm)
      (some ((MixedCode.encoding.list.encode (components g)).map componentsRawComputer.outputAlphabet.symm))
      (componentsRawComputer.time.eval raw.length) := by
  let w : BitEncoding.ValidWord MixedCode.encoding := ⟨raw,⟨g,hd⟩⟩
  have hv : w.value = g := BitEncoding.ValidWord.value_eq hd
  have h := componentsRawComputer.outputsFun w
  simpa only [BitEncoding.toFinEncoding,BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw,hv,w] using h

end PlanarHom.GraphComponentMachines
