import PlanarHom.FreshDomainOccurrenceSemantics
import PlanarHom.PrescribedDomainQueryPromises
import PlanarHom.SelectedStretchAppend

/-! Prescribed-domain path queries keep the old domains and give each new vertex
one intrinsic full-domain record. Path typing is an explicit hypothesis on the
fixed source language, including length-one and both boundary segments. -/

namespace PlanarHom.Complexity.MixedCode
open PairProjectionMachines

/-- The full prescribed-domain query, with its original metadata prefix and
exactly one fresh intrinsic domain record per allocated path vertex. -/
def stretchLabelDomains (g : MixedCode) (selected replacement domainLabel n : ℕ) : MixedCode :=
  (g.stretchLabel selected replacement n).withFreshDomains g.vertices domainLabel

theorem stretchLabelDomains_valid {a b u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (selected replacement domainLabel n : ℕ) (hr : replacement<b) (hd : domainLabel<u)
    (hkeep : ∀ e∈g.edges,e.2.2≠selected→e.2.2<b) :
    (g.stretchLabelDomains selected replacement domainLabel n).Valid b u :=
  withFreshDomains_valid _ (g.stretchLabel_valid hg selected replacement n hr hkeep)
    g.vertices domainLabel hd

theorem fp_stretchLabelDomains (selected replacement domainLabel : ℕ) :
    FP (BitEncoding.unaryNat.prod encoding) encoding
      (fun p => p.2.stretchLabelDomains selected replacement domainLabel p.1) :=
  ((((fp_snd BitEncoding.unaryNat encoding).comp fp_vertices).pair
    (fp_stretchLabel selected replacement)).comp (fp_withFreshDomains domainLabel))

noncomputable def stretchLabelDomainsComputer (selected replacement domainLabel : ℕ) :
    Turing.TM2ComputableInPolyTime (BitEncoding.unaryNat.prod encoding).toFinEncoding
      encoding.toFinEncoding
      (fun p => p.2.stretchLabelDomains selected replacement domainLabel p.1) :=
  Classical.choice (fp_stretchLabelDomains selected replacement domainLabel)

noncomputable def stretchLabelDomainsRawComputer (selected replacement domainLabel : ℕ) :
    Turing.TM2ComputableInPolyTime
      (BitEncoding.ValidWord.encoding (BitEncoding.unaryNat.prod encoding)).toFinEncoding
      encoding.toFinEncoding
      (fun w => w.value.2.stretchLabelDomains selected replacement domainLabel w.value.1) :=
  MachineComposition.composeComputers
    (BitEncoding.prodNormalizer BitEncoding.unaryNormalizer normalizer)
    (stretchLabelDomainsComputer selected replacement domainLabel)

/-- The actual raw machine consumes every decodable parameter/graph word, not
only the canonical encoding. -/
noncomputable def stretchLabelDomains_raw_outputs (selected replacement domainLabel : ℕ)
    (raw : Bits) (n : ℕ) (g : MixedCode)
    (hd : (BitEncoding.unaryNat.prod encoding).decode raw=some (n,g)) :
    Turing.TM2OutputsInTime (stretchLabelDomainsRawComputer selected replacement domainLabel).tm
      (raw.map (stretchLabelDomainsRawComputer selected replacement domainLabel).inputAlphabet.symm)
      (some ((encoding.encode (g.stretchLabelDomains selected replacement domainLabel n)).map
        (stretchLabelDomainsRawComputer selected replacement domainLabel).outputAlphabet.symm))
      ((stretchLabelDomainsRawComputer selected replacement domainLabel).time.eval raw.length) := by
  let w : BitEncoding.ValidWord (BitEncoding.unaryNat.prod encoding) := ⟨raw,⟨(n,g),hd⟩⟩
  have hv : w.value=(n,g) := BitEncoding.ValidWord.value_eq hd
  have h := (stretchLabelDomainsRawComputer selected replacement domainLabel).outputsFun w
  simpa only [BitEncoding.toFinEncoding, BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw, w, hv] using h

/-- Positive path length `h` is represented by `h-1` fresh vertices per edge. -/
def stretchLabelDomainsLength (g : MixedCode) (selected replacement domainLabel h : ℕ) : MixedCode :=
  g.stretchLabelDomains selected replacement domainLabel (h-1)

theorem fp_stretchLabelDomainsLength (selected replacement domainLabel : ℕ) :
    FP (BitEncoding.unaryNat.prod encoding) encoding
      (fun p => p.2.stretchLabelDomainsLength selected replacement domainLabel p.1) :=
  ((((fp_fst BitEncoding.unaryNat encoding).comp UnaryArithmeticMachines.fp_pred).pair
    (fp_snd BitEncoding.unaryNat encoding)).comp
      (fp_stretchLabelDomains selected replacement domainLabel))

noncomputable def stretchLabelDomainsLengthComputer (selected replacement domainLabel : ℕ) :
    Turing.TM2ComputableInPolyTime (BitEncoding.unaryNat.prod encoding).toFinEncoding
      encoding.toFinEncoding
      (fun p => p.2.stretchLabelDomainsLength selected replacement domainLabel p.1) :=
  Classical.choice (fp_stretchLabelDomainsLength selected replacement domainLabel)

noncomputable def stretchLabelDomainsLengthRawComputer (selected replacement domainLabel : ℕ) :
    Turing.TM2ComputableInPolyTime
      (BitEncoding.ValidWord.encoding (BitEncoding.unaryNat.prod encoding)).toFinEncoding
      encoding.toFinEncoding
      (fun w => w.value.2.stretchLabelDomainsLength selected replacement domainLabel w.value.1) :=
  MachineComposition.composeComputers
    (BitEncoding.prodNormalizer BitEncoding.unaryNormalizer normalizer)
    (stretchLabelDomainsLengthComputer selected replacement domainLabel)

noncomputable def stretchLabelDomainsLength_raw_outputs (selected replacement domainLabel : ℕ)
    (raw : Bits) (h : ℕ) (g : MixedCode)
    (hd : (BitEncoding.unaryNat.prod encoding).decode raw=some (h,g)) :
    Turing.TM2OutputsInTime (stretchLabelDomainsLengthRawComputer selected replacement domainLabel).tm
      (raw.map (stretchLabelDomainsLengthRawComputer selected replacement domainLabel).inputAlphabet.symm)
      (some ((encoding.encode (g.stretchLabelDomainsLength selected replacement domainLabel h)).map
        (stretchLabelDomainsLengthRawComputer selected replacement domainLabel).outputAlphabet.symm))
      ((stretchLabelDomainsLengthRawComputer selected replacement domainLabel).time.eval raw.length) := by
  let w : BitEncoding.ValidWord (BitEncoding.unaryNat.prod encoding) := ⟨raw,⟨(h,g),hd⟩⟩
  have hv : w.value=(h,g) := BitEncoding.ValidWord.value_eq hd
  have hout := (stretchLabelDomainsLengthRawComputer selected replacement domainLabel).outputsFun w
  simpa only [BitEncoding.toFinEncoding, BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw, w, hv] using hout

end PlanarHom.Complexity.MixedCode

namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode
variable {a b u d : ℕ}

/-- The four ordered endpoint pairs that can occur in a positive-length path.
This hypothesis is required: arbitrary endpoint-domain tables need not be closed
under replacing an auxiliary occurrence by a path. -/
def PathDomainTyping (B : Fin b → Fin d → Fin d → Prop)
    (replacement : Fin b) (full x y : Fin d) : Prop :=
  B replacement x y ∧ B replacement x full ∧
    B replacement full full ∧ B replacement full y

private theorem pathSegment_typed
    (B : Fin b → Fin d → Fin d → Prop) (replacement : Fin b)
    {oldV newV : ℕ} (δ : Fin oldV → Fin d) (full : Fin d)
    (e : (ℕ × (ℕ × ℕ)) × ℕ) (n k : ℕ)
    (hs : e.1.1<oldV) (ht : e.1.2.1<oldV)
    (hv : (pathSegment oldV replacement.val n e k).1<newV ∧
      (pathSegment oldV replacement.val n e k).2.1<newV)
    (h : PathDomainTyping B replacement full (δ ⟨e.1.1,hs⟩) (δ ⟨e.1.2.1,ht⟩)) :
    B replacement
      (extendAssignment δ full ⟨(pathSegment oldV replacement.val n e k).1,hv.1⟩)
      (extendAssignment δ full ⟨(pathSegment oldV replacement.val n e k).2.1,hv.2⟩) := by
  rcases h with ⟨hxy,hxf,hff,hfy⟩
  by_cases hzero : k=0 <;> by_cases hlast : k=n
  · simpa only [pathSegment,if_pos hzero,if_pos hlast,extendAssignment,dif_pos hs,dif_pos ht] using hxy
  · have hf : ¬oldV+e.2*n+k<oldV := by omega
    simpa only [pathSegment,if_pos hzero,if_neg hlast,extendAssignment,dif_pos hs,dif_neg hf] using hxf
  · have hf : ¬oldV+e.2*n+(k-1)<oldV := by omega
    simpa only [pathSegment,if_neg hzero,if_pos hlast,extendAssignment,dif_pos ht,dif_neg hf] using hfy
  · have hf : ¬oldV+e.2*n+(k-1)<oldV := by omega
    have hf' : ¬oldV+e.2*n+k<oldV := by omega
    simpa only [pathSegment,if_neg hzero,if_neg hlast,extendAssignment,dif_neg hf,dif_neg hf'] using hff

/-- Every segment is checked against the same fixed source tables. Old vertices
retain δ; all private path vertices have the single prescribed domain `full`. -/
theorem Typed.stretchLabel
    {BT : Fin a → Fin d → Fin d → Prop} {BS : Fin b → Fin d → Fin d → Prop}
    {U : Fin u → Fin d → Prop} (selected : Fin a) (replacement : Fin b) (full : Fin d)
    (hkeep : ∀ i : Fin a, i.val≠selected.val → i.val<b)
    (hcomp : ∀ (i : Fin a) (hi : i.val≠selected.val) x y,
      BT i x y → BS ⟨i.val,hkeep i hi⟩ x y)
    (hpath : ∀ x y, BT selected x y → PathDomainTyping BS replacement full x y)
    {g : MixedCode} {hg : g.Valid a u} {δ : Fin g.vertices → Fin d}
    (h : Typed BT U g hg δ) (n : ℕ) :
    Typed BS U (g.stretchLabel selected.val replacement.val n)
      (g.stretchLabel_valid hg selected.val replacement.val n replacement.isLt
        (fun e he hn => hkeep ⟨e.2.2,(hg.1 e he).2.2⟩ hn))
      (extendAssignment δ full) := by
  let hout := g.stretchLabel_valid hg selected.val replacement.val n replacement.isLt
    (fun e he hn => hkeep ⟨e.2.2,(hg.1 e he).2.2⟩ hn)
  constructor
  · intro e he
    have he' := he
    rw [stretchLabel_edges_eq_flatMap] at he'
    rcases List.mem_append.mp he' with hp | hc
    · obtain ⟨item,hitem,hseg⟩ := List.mem_flatMap.mp hp
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hseg
      have hmem : item.1 ∈ g.selectedEdges selected.val := by
        exact List.fst_mem_of_mem_zipIdx hitem
      have ho := (List.mem_filter.mp hmem).1
      have hl : item.1.2.2=selected.val := by simpa using (List.mem_filter.mp hmem).2
      have hv := hg.1 item.1 ho
      have htyped := h.1 item.1 ho
      have hi : (⟨item.1.2.2,hv.2.2⟩ : Fin a)=selected := Fin.ext hl
      rw [hi] at htyped
      have hh := pathSegment_typed BS replacement δ full item n k hv.1 hv.2.1
        ⟨(hout.1 _ he).1,(hout.1 _ he).2.1⟩ (hpath _ _ htyped)
      exact hh
    · have ho := (List.mem_filter.mp hc).1
      have hn : e.2.2≠selected.val := by simpa using (List.mem_filter.mp hc).2
      have hv := hg.1 e ho
      simpa only [extendAssignment, dif_pos hv.1, dif_pos hv.2.1] using
          hcomp ⟨e.2.2,hv.2.2⟩ hn _ _ (h.1 e ho)
  · intro e he
    have hv := hg.2 e he
    simpa only [extendAssignment, dif_pos hv.1] using h.2 e he

/-- Exact code equality, including the order and count of reserved metadata. -/
theorem stretchLabelDomains_withDomains (g : MixedCode) (δ : Fin g.vertices → Fin d)
    (full : Fin d) (selected replacement n : ℕ) :
    (withDomains (unaryTypes:=u) g δ).stretchLabelDomains selected replacement (u+full.val) n =
      withDomains (unaryTypes:=u) (g.stretchLabel selected replacement n) (extendAssignment δ full) :=
  stretchLabel_withDomains g δ full selected replacement n

/-- Every actual domain-aware path query again has the exact encoded-input
promise, with unchanged companion labels and ordinary unary typing. -/
theorem EncodedGraph.stretchLabelDomains
    {BT : Fin a → Fin d → Fin d → Prop} {BS : Fin b → Fin d → Fin d → Prop}
    {U : Fin u → Fin d → Prop} (selected : Fin a) (replacement : Fin b) (full : Fin d)
    (hkeep : ∀ i : Fin a, i.val≠selected.val → i.val<b)
    (hcomp : ∀ (i : Fin a) (hi : i.val≠selected.val) x y,
      BT i x y → BS ⟨i.val,hkeep i hi⟩ x y)
    (hpath : ∀ x y, BT selected x y → PathDomainTyping BS replacement full x y)
    {g : MixedCode} (h : EncodedGraph BT U g) (n : ℕ) :
    EncodedGraph BS U (g.stretchLabelDomains selected.val replacement.val (u+full.val) n) := by
  obtain ⟨original,hg,δ,ht,hp,hd⟩ := h
  rw [MixedCode.encoding.decode_encode] at hd
  have he : g=withDomains (unaryTypes:=u) original δ := Option.some.inj hd
  subst g
  unfold EncodedGraph
  rw [stretchLabelDomains_withDomains]
  exact encodedInput_encode_withDomains (ht.stretchLabel selected replacement full hkeep hcomp hpath n)
    (original.stretchLabel_planar ⟨hg,hp⟩ selected.val replacement.val n replacement.isLt
      (fun e he hn => hkeep ⟨e.2.2,(hg.1 e he).2.2⟩ hn)).2

/-- Promise preservation also starts from arbitrary successfully decoded raw
input words. The emitted word is the real machine's canonical output. -/
theorem EncodedInput.stretchLabelDomains
    {BT : Fin a → Fin d → Fin d → Prop} {BS : Fin b → Fin d → Fin d → Prop}
    {U : Fin u → Fin d → Prop} (selected : Fin a) (replacement : Fin b) (full : Fin d)
    (hkeep : ∀ i : Fin a, i.val≠selected.val → i.val<b)
    (hcomp : ∀ (i : Fin a) (hi : i.val≠selected.val) x y,
      BT i x y → BS ⟨i.val,hkeep i hi⟩ x y)
    (hpath : ∀ x y, BT selected x y → PathDomainTyping BS replacement full x y)
    {raw : Bits} {g : MixedCode} (hd : MixedCode.encoding.decode raw=some g)
    (h : EncodedInput BT U raw) (n : ℕ) :
    EncodedInput BS U (MixedCode.encoding.encode
      (g.stretchLabelDomains selected.val replacement.val (u+full.val) n)) := by
  have hg : EncodedGraph BT U g :=
    (encodedInput_congr_decode BT U (hd.trans (MixedCode.encoding.decode_encode g).symm)).mp h
  exact hg.stretchLabelDomains selected replacement full hkeep hcomp hpath n

/-- For an appended auxiliary type, every companion is already an original
source type. The distinguished source matrix is `oldC`. -/
theorem Typed.stretchAppendedAuxiliary
    {B : Fin b → Fin d → Fin d → Prop} {A : Fin d → Fin d → Prop}
    {U : Fin u → Fin d → Prop} (oldC : Fin b) (full : Fin d)
    (hpath : ∀ x y, A x y → PathDomainTyping B oldC full x y)
    {g : MixedCode} {hg : g.Valid (b+1) u} {δ : Fin g.vertices → Fin d}
    (h : Typed (FiniteLanguageAliases.appendOne B A) U g hg δ) (n : ℕ) :
    Typed B U (g.stretchLabel b oldC.val n)
      (g.stretchLabel_valid hg b oldC.val n oldC.isLt (g.appended_companion_bound hg))
      (extendAssignment δ full) := by
  have hkeep : ∀ i : Fin (b+1), i.val≠(Fin.last b).val → i.val<b := by
    intro i hi
    have := i.isLt
    simp only [Fin.val_last] at hi
    omega
  refine h.stretchLabel (Fin.last b) oldC full hkeep ?_ ?_ n
  · intro i hi x y hB
    have he : i=Fin.castAdd 1 ⟨i.val,hkeep i hi⟩ := Fin.ext rfl
    rw [he,FiniteLanguageAliases.appendOne_old] at hB
    exact hB
  · simpa only [FiniteLanguageAliases.appendOne_aux] using hpath

/-- The ordinary source alphabet has `b` labels; only the appended last label
is replaced, and its C-path queries satisfy the exact prescribed-domain promise. -/
theorem EncodedGraph.stretchAppendedAuxiliary
    {B : Fin b → Fin d → Fin d → Prop} {A : Fin d → Fin d → Prop}
    {U : Fin u → Fin d → Prop} (oldC : Fin b) (full : Fin d)
    (hpath : ∀ x y, A x y → PathDomainTyping B oldC full x y)
    {g : MixedCode} (h : EncodedGraph (FiniteLanguageAliases.appendOne B A) U g) (n : ℕ) :
    EncodedGraph B U (g.stretchLabelDomains b oldC.val (u+full.val) n) := by
  have hkeep : ∀ i : Fin (b+1), i.val≠(Fin.last b).val → i.val<b := by
    intro i hi
    have := i.isLt
    simp only [Fin.val_last] at hi
    omega
  apply h.stretchLabelDomains (Fin.last b) oldC full hkeep
  · intro i hi x y hB
    have he : i=Fin.castAdd 1 ⟨i.val,hkeep i hi⟩ := Fin.ext rfl
    rw [he,FiniteLanguageAliases.appendOne_old] at hB
    exact hB
  · simpa only [FiniteLanguageAliases.appendOne_aux] using hpath

/-- The positive-length interface preserves the exact source promise too. -/
theorem EncodedInput.stretchAppendedAuxiliaryLength
    {B : Fin b → Fin d → Fin d → Prop} {A : Fin d → Fin d → Prop}
    {U : Fin u → Fin d → Prop} (oldC : Fin b) (full : Fin d)
    (hpath : ∀ x y, A x y → PathDomainTyping B oldC full x y)
    {raw : Bits} {g : MixedCode} (hd : MixedCode.encoding.decode raw=some g)
    (h : EncodedInput (FiniteLanguageAliases.appendOne B A) U raw) (length : ℕ) :
    EncodedInput B U (MixedCode.encoding.encode
      (g.stretchLabelDomainsLength b oldC.val (u+full.val) length)) := by
  have hg : EncodedGraph (FiniteLanguageAliases.appendOne B A) U g :=
    (encodedInput_congr_decode _ U (hd.trans (MixedCode.encoding.decode_encode g).symm)).mp h
  exact hg.stretchAppendedAuxiliary oldC full hpath (length-1)

/-- The designated intrinsic full-domain label evaluates to one on every color. -/
theorem extendedUnaries_full {C R : Type} [CommSemiring R]
    (U : Fin u → C → R) (D : Fin d → Set C) (full : Fin d)
    (hfull : D full=Set.univ) (c : C) :
    extendedUnaries U D (Fin.natAdd u full) c=1 := by
  classical
  rw [extendedUnaries,Fin.addCases_right,hfull]
  simp [indicator]

/-- Full-domain metadata contributes factor one, so the actual compiled query
has precisely the restricted-domain path-power value. -/
theorem evaluate_stretchLabelDomains_withDomains {C R : Type} [Fintype C] [DecidableEq C] [CommSemiring R]
    (g : MixedCode) (hg : g.Valid (b+1) u) (replacement : Fin b) (n : ℕ)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R)
    (D : Fin d → Set C) (δ : Fin g.vertices → Fin d) (full : Fin d)
    (hfull : D full=Set.univ) :
    ((withDomains (unaryTypes:=u) g δ).stretchLabelDomains b replacement.val (u+full.val) n).evaluate
      ((withDomains (unaryTypes:=u) g δ).stretchLabelDomains_valid (withDomains_valid g hg δ)
        b replacement.val (u+full.val) n replacement.isLt (Nat.add_lt_add_left full.isLt u)
        ((withDomains (unaryTypes:=u) g δ).appended_companion_bound (withDomains_valid g hg δ)))
      M (extendedUnaries U D) (fun _ => 1) =
    evaluateRestricted g hg (FiniteLanguageAliases.appendOne M (M replacement^(n+1)))
      U (fun _ => 1) D δ := by
  let G := withDomains (unaryTypes:=u) g δ
  let hG := withDomains_valid g hg δ
  have hf := (G.stretchLabel b replacement.val n).evaluate_withFreshDomains
    (G.stretchLabel_valid hG b replacement.val n replacement.isLt (G.appended_companion_bound hG))
    G.vertices (Fin.natAdd u full) M (extendedUnaries U D) (fun _ => 1)
    (extendedUnaries_full U D full hfull)
  exact hf.trans ((G.evaluate_stretchLabel_appendOne hG replacement n M (extendedUnaries U D)).trans
    (evaluate_withDomains g hg _ U (fun _ => 1) D δ))

/-- Rewriting the literal code commutation gives the intrinsic restricted-sum
identity for the extended assignment itself. -/
theorem evaluateRestricted_stretchLabel {C R : Type} [Fintype C] [DecidableEq C] [CommSemiring R]
    (g : MixedCode) (hg : g.Valid (b+1) u) (replacement : Fin b) (n : ℕ)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R)
    (D : Fin d → Set C) (δ : Fin g.vertices → Fin d) (full : Fin d)
    (hfull : D full=Set.univ) :
    evaluateRestricted (g.stretchLabel b replacement.val n)
      (g.stretchLabel_valid hg b replacement.val n replacement.isLt (g.appended_companion_bound hg))
      M U (fun _ => 1) D (extendAssignment δ full) =
    evaluateRestricted g hg (FiniteLanguageAliases.appendOne M (M replacement^(n+1)))
      U (fun _ => 1) D δ := by
  have h := evaluate_stretchLabelDomains_withDomains g hg replacement n M U D δ full hfull
  have he := stretchLabelDomains_withDomains (u:=u) g δ full b replacement.val n
  have hvalue : ((withDomains (unaryTypes:=u) g δ).stretchLabelDomains b replacement.val
      (u+full.val) n).evaluate
      ((withDomains (unaryTypes:=u) g δ).stretchLabelDomains_valid (withDomains_valid g hg δ)
        b replacement.val (u+full.val) n replacement.isLt (Nat.add_lt_add_left full.isLt u)
        ((withDomains (unaryTypes:=u) g δ).appended_companion_bound (withDomains_valid g hg δ)))
      M (extendedUnaries U D) (fun _ => 1) =
      (withDomains (unaryTypes:=u) (g.stretchLabel b replacement.val n)
        (extendAssignment δ full)).evaluate
        (withDomains_valid _ (g.stretchLabel_valid hg b replacement.val n replacement.isLt
          (g.appended_companion_bound hg)) (extendAssignment δ full))
        M (extendedUnaries U D) (fun _ => 1) := by
    simp only [MixedCode.evaluate]
    rw [he]
  rw [hvalue,evaluate_withDomains] at h
  exact h

/-- For every positive sample length, the restricted-domain exponent equals
that length, with the same color coordinates and unit background. -/
theorem evaluateRestricted_stretchLabelLength {C R : Type} [Fintype C] [DecidableEq C] [CommSemiring R]
    (g : MixedCode) (hg : g.Valid (b+1) u) (replacement : Fin b) (length : ℕ) (hl : 1≤length)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R)
    (D : Fin d → Set C) (δ : Fin g.vertices → Fin d) (full : Fin d)
    (hfull : D full=Set.univ) :
    evaluateRestricted (g.stretchLabelLength b replacement.val length)
      (g.stretchLabelLength_valid hg b length replacement (g.appended_companion_bound hg))
      M U (fun _ => 1) D (extendAssignment δ full) =
    evaluateRestricted g hg (FiniteLanguageAliases.appendOne M (M replacement^length))
      U (fun _ => 1) D δ := by
  simpa only [stretchLabelLength,Nat.sub_add_cancel hl] using
    evaluateRestricted_stretchLabel g hg replacement (length-1) M U D δ full hfull

end PlanarHom.PrescribedDomains
