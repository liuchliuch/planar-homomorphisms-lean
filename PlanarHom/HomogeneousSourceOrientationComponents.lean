import PlanarHom.HomogeneousSourceOrientationConnected
import PlanarHom.GraphComponentReduction
import Mathlib.Data.List.Perm.Subperm

/-! Concrete component metadata canonicalization. Extraction preserves each
intrinsic domain occurrence but changes its order; the following lookup and
canonicalization programs restore the exact prescribed-domain code order. -/
noncomputable section
namespace PlanarHom.HomogeneousSourceOrientation
open Complexity Complexity.MixedCode PrescribedDomains GraphComponentCode
open PairProjectionMachines ArithmeticCircuitPrimitives

abbrev unaryCode := BitEncoding.nat.prod BitEncoding.nat

def tagAt (g : MixedCode) (v : ℕ) : ℕ :=
  ((g.unaries.filter (fun u => decide (u.1 = v))).headD (0,0)).2

def canonicalDomains (g : MixedCode) : MixedCode :=
  ⟨g.vertices, g.edges, (List.range g.vertices).map (fun v => (v,tagAt g v))⟩

theorem fp_tagAt : FP (MixedCode.encoding.prod BitEncoding.nat) BitEncoding.nat
    (fun p => tagAt p.1 p.2) := by
  have hg := fp_fst MixedCode.encoding BitEncoding.nat
  have hv := fp_snd MixedCode.encoding BitEncoding.nat
  have htest : FP (BitEncoding.nat.prod unaryCode) BitEncoding.bool
      (fun p => decide (p.2.1 = p.1)) :=
    (((fp_snd BitEncoding.nat unaryCode).comp (fp_fst BitEncoding.nat BitEncoding.nat)).pair
      (fp_fst BitEncoding.nat unaryCode)).comp NatListSumMachines.fp_equal
  have hf := (hv.pair (hg.comp MixedCode.fp_unaries)).comp
    (ListContextFilterMachines.fp_filterWithContext BitEncoding.nat unaryCode _ htest)
  exact ((hf.comp (ListDecompositionMachines.fp_headD unaryCode (0,0))).comp
    (fp_snd BitEncoding.nat BitEncoding.nat))

theorem fp_canonicalDomains : FP MixedCode.encoding MixedCode.encoding canonicalDomains := by
  have hr := (MixedCode.fp_vertices.comp UnaryRangeMachines.fp_range).comp
    (ListReverseMachines.fp_reverse BitEncoding.nat)
  have hrecord := (fp_snd MixedCode.encoding BitEncoding.nat).pair fp_tagAt
  have hu := ((fp_id MixedCode.encoding).pair hr).comp
    (ListContextMachines.fp_mapWithContext MixedCode.encoding BitEncoding.nat unaryCode _ hrecord)
  exact ((MixedCode.fp_vertices.pair (MixedCode.fp_edges.pair hu)).transportOutput
    (fun g => by simp only [Function.comp_apply, id_eq, List.reverse_reverse]; rfl))

/-- A permutation is allowed only in the order of the one-per-vertex intrinsic
records. Neither additional unary factors nor repeated tags are introduced. -/
def Tags (g : MixedCode) (δ : Fin g.vertices → Fin 2) : Prop :=
  g.unaries.Perm (domainOccurrences (unaryTypes := 0) g δ)

theorem domainOccurrences_nodup (g : MixedCode) (δ : Fin g.vertices → Fin 2) :
    (domainOccurrences (unaryTypes := 0) g δ).Nodup := by
  apply List.nodup_ofFn.mpr
  intro a b h
  exact Fin.ext (congrArg Prod.fst h)

theorem tagAt_of_tags (g : MixedCode) (δ : Fin g.vertices → Fin 2)
    (ht : Tags g δ) (v : Fin g.vertices) : tagAt g v.val = (δ v).val := by
  let p : ℕ × ℕ → Bool := fun u => decide (u.1 = v.val)
  have hperm := ht.filter p
  have hn := (domainOccurrences_nodup g δ).filter p
  have he : ((domainOccurrences (unaryTypes := 0) g δ).filter p).Perm [(v.val,(δ v).val)] := by
    apply (List.perm_ext_iff_of_nodup hn (List.nodup_singleton _)).mpr
    intro u
    simp only [List.mem_filter, domainOccurrences, List.mem_ofFn, List.mem_singleton]
    constructor
    · rintro ⟨⟨a,rfl⟩, ha⟩
      have hav : a = v := Fin.ext (of_decide_eq_true ha)
      subst a
      simp only [Nat.zero_add]
    · intro hu
      subst u
      exact ⟨⟨v, by simp only [Nat.zero_add]⟩, by simp only [p, decide_true]⟩
  have hfilter := List.perm_singleton.mp (hperm.trans he)
  change ((g.unaries.filter p).headD (0,0)).2 = _
  rw [hfilter]
  rfl

theorem canonicalDomains_eq (g : MixedCode) (δ : Fin g.vertices → Fin 2)
    (ht : Tags g δ) : canonicalDomains g = withDomains (unaryTypes := 0) (eraseDomains g) δ := by
  unfold canonicalDomains withDomains eraseDomains
  congr 1
  change (List.range g.vertices).map (fun v => (v,tagAt g v)) =
      [] ++ domainOccurrences (unaryTypes := 0) (eraseDomains g) δ
  rw [List.nil_append]
  unfold domainOccurrences
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_ofFn]; rfl
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, Nat.zero_add]
    exact congrArg (fun n => (i,n)) (tagAt_of_tags g δ ht ⟨i, by simpa using hi⟩)

/-- Original vertex at the computed local list position. -/
def localVertex (g : MixedCode) (xs : List ℕ)
    (hb : ∀ v ∈ xs, v < g.vertices) (v : Fin xs.length) : Fin g.vertices :=
  ⟨xs.get v, hb _ (List.get_mem _ _)⟩

theorem localVertex_index (g : MixedCode) (xs : List ℕ)
    (hb : ∀ v ∈ xs, v < g.vertices) (i : Fin g.vertices) (hi : i.val ∈ xs) :
    localVertex g xs hb ⟨xs.idxOf i.val, List.idxOf_lt_length_iff.mpr hi⟩ = i := by
  apply Fin.ext
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hi)

/-- Stable component extraction preserves exactly one intrinsic record per
local vertex, although the order may change. -/
theorem extract_tags (g : MixedCode) (δ : Fin g.vertices → Fin 2)
    (ht : Tags g δ) (xs : List ℕ) (hxs : xs.Nodup)
    (hb : ∀ v ∈ xs, v < g.vertices) :
    Tags (extract g xs) (fun v => δ (localVertex g xs hb v)) := by
  have hn : (extract g xs).unaries.Nodup := by
    apply List.Nodup.map_on ?_ ((ht.nodup_iff.mpr (domainOccurrences_nodup g δ)).filter _)
    intro a ha b hbb he
    have ha' : a.1 ∈ xs := of_decide_eq_true (List.mem_filter.mp ha).2
    have hb' : b.1 ∈ xs := of_decide_eq_true (List.mem_filter.mp hbb).2
    have hh := Prod.mk.inj he
    exact Prod.ext ((List.idxOf_inj ha' hb').mp hh.1) hh.2
  apply (List.perm_ext_iff_of_nodup hn (domainOccurrences_nodup _ _)).mpr
  intro u
  constructor
  · intro hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
    obtain ⟨ha, hai⟩ := List.mem_filter.mp ha
    have hai' : a.1 ∈ xs := of_decide_eq_true hai
    have ham := ht.mem_iff.mp ha
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp ham
    change (i.val, 0 + (δ i).val) = a at hi
    simp only [Nat.zero_add] at hi
    subst a
    apply List.mem_ofFn.mpr
    refine ⟨⟨xs.idxOf i.val, List.idxOf_lt_length_iff.mpr hai'⟩, ?_⟩
    simp only [localVertex_index g xs hb i hai', Nat.zero_add]
  · intro hu
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hu
    apply List.mem_map.mpr
    refine ⟨((localVertex g xs hb v).val, (δ (localVertex g xs hb v)).val), ?_, ?_⟩
    · apply List.mem_filter.mpr
      constructor
      · apply ht.mem_iff.mpr
        exact List.mem_ofFn.mpr ⟨localVertex g xs hb v, by simp only [Nat.zero_add]⟩
      · exact decide_eq_true (List.get_mem xs v)
    · change (xs.idxOf (xs.get v), _) = (v.val, 0 + _)
      rw [List.get_idxOf hxs v, Nat.zero_add]

@[simp] theorem canonicalDomains_vertices (g : MixedCode) : (canonicalDomains g).vertices = g.vertices := rfl
@[simp] theorem canonicalDomains_edges (g : MixedCode) : (canonicalDomains g).edges = g.edges := rfl
@[simp] theorem canonicalDomains_support (g : MixedCode) : support (canonicalDomains g) = support g := rfl
@[simp] theorem canonicalDomains_underlying (g : MixedCode) :
    (canonicalDomains g).underlying = g.underlying := rfl

theorem eraseDomains_valid {b u : ℕ} (g : MixedCode) (hg : g.Valid b u) :
    (eraseDomains g).Valid b 0 := ⟨hg.1, by simp only [eraseDomains, List.not_mem_nil, false_implies, implies_true]⟩

theorem canonicalDomains_valid {b : ℕ} (g : MixedCode) (hg : g.Valid b 2)
    (δ : Fin g.vertices → Fin 2) (ht : Tags g δ) : (canonicalDomains g).Valid b 2 := by
  rw [canonicalDomains_eq g δ ht]
  exact withDomains_valid _ (eraseDomains_valid g hg) δ

theorem canonicalDomains_unaries (g : MixedCode) (δ : Fin g.vertices → Fin 2)
    (ht : Tags g δ) : (canonicalDomains g).unaries = domainOccurrences (unaryTypes := 0) g δ := by
  have hh := congrArg MixedCode.unaries (canonicalDomains_eq g δ ht)
  exact hh

/-- Canonicalization changes only record order, hence retains every exact
assignment contribution and all cancellation. -/
theorem canonicalDomains_evaluate {C R : Type} [Fintype C] [CommSemiring R] {b : ℕ}
    (g : MixedCode) (hg : g.Valid b 2) (δ : Fin g.vertices → Fin 2) (ht : Tags g δ)
    (M : Fin b → Matrix C C R) (U : Fin 2 → C → R) (w : C → R) :
    totalEvaluation M U w (canonicalDomains g) = totalEvaluation M U w g := by
  rw [totalEvaluation_valid _ _ _ _ (canonicalDomains_valid g hg δ ht),
    totalEvaluation_valid _ _ _ _ hg]
  unfold evaluate
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [canonicalDomains_unaries g δ ht]
  exact (ht.symm.map (unaryValue g.vertices 2 U σ)).prod_eq

theorem extract_typed (g : MixedCode) (hg : g.Valid 1 0)
    (δ : Fin g.vertices → Fin 2) (ht : Typed sidePolicies emptyPolicies g hg δ)
    (xs : List ℕ) (hb : ∀ v ∈ xs, v < g.vertices) :
    Typed sidePolicies emptyPolicies (extract g xs) (extract_valid g hg xs)
      (fun v => δ (localVertex g xs hb v)) := by
  constructor
  · intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨ha, hai⟩ := List.mem_filter.mp ha
    have hai' : a.1 ∈ xs ∧ a.2.1 ∈ xs := of_decide_eq_true hai
    have h := ht.1 a ha
    change δ (localVertex g xs hb _) ≠ δ (localVertex g xs hb _)
    rw [localVertex_index g xs hb ⟨a.1,(hg.1 a ha).1⟩ hai'.1,
      localVertex_index g xs hb ⟨a.2.1,(hg.1 a ha).2.1⟩ hai'.2]
    exact h
  · intro u hu
    exact False.elim (Nat.not_lt_zero _ ((extract_valid g hg xs).2 u hu).2)

theorem tags_withDomains (g : MixedCode) (hg : g.Valid 1 0)
    (δ : Fin g.vertices → Fin 2) : Tags (withDomains (unaryTypes := 0) g δ) δ := by
  unfold Tags withDomains
  rw [unaries_nil_of_valid_zero g hg, List.nil_append]
  exact List.Perm.refl _

theorem eraseDomains_extract_withDomains (g : MixedCode) (hg : g.Valid 1 0)
    (δ : Fin g.vertices → Fin 2) (xs : List ℕ) :
    eraseDomains (extract (withDomains (unaryTypes := 0) g δ) xs) = extract g xs := by
  unfold eraseDomains extract withDomains
  rw [unaries_nil_of_valid_zero g hg]
  rfl

/-- Every computed component can be serialized back in the exact original
typed-domain format by the concrete canonicalization program. -/
theorem canonical_components_promises (code : MixedCode)
    (hc : EncodedGraph sidePolicies emptyPolicies code) :
    ∀ c ∈ components code, connectedTypedGraph (canonicalDomains c) := by
  intro c hm
  obtain ⟨g,hg,δ,ht,hp,hd⟩ := hc
  rw [MixedCode.encoding.decode_encode] at hd
  have heq := Option.some.inj hd
  subst code
  obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hm
  have hx : xs ∈ parts g := hxs
  have hnd := part_nodup g xs hx
  have hb := part_vertex_lt g xs hx
  let δ' : Fin xs.length → Fin 2 := fun v => δ (localVertex g xs hb v)
  have htags : Tags (extract (withDomains (unaryTypes := 0) g δ) xs) δ' :=
    extract_tags (withDomains (unaryTypes := 0) g δ) δ (tags_withDomains g hg δ) xs hnd hb
  rw [canonicalDomains_eq _ δ' htags]
  have he : withDomains (unaryTypes := 0) (eraseDomains (extract (withDomains (unaryTypes := 0) g δ) xs)) δ' =
      withDomains (unaryTypes := 0) (extract g xs) δ' := by
    unfold withDomains eraseDomains extract
    rw [unaries_nil_of_valid_zero g hg]
    rfl
  rw [he]
  refine ⟨?_,?_,?_⟩
  · exact encodedInput_encode_withDomains (extract_typed g hg δ ht xs hb)
      (extract_planarValid g ⟨hg,hp⟩ xs hnd hb).2
  · exact extract_connected g hg xs hx
  · exact List.length_pos_iff.mpr (parts_nonempty g xs hx)

/-- The complete computed component batch preserves the exact value, including
zero vertices and all isolated vertices. -/
theorem canonical_components_evaluate {C R : Type} [Fintype C] [CommSemiring R]
    (code : MixedCode) (hc : EncodedGraph sidePolicies emptyPolicies code)
    (M : Fin 1 → Matrix C C R) (U : Fin 2 → C → R) (w : C → R) :
    ((components code).map (fun c => totalEvaluation M U w (canonicalDomains c))).prod =
      code.evaluate hc.planarValid.1 M U w := by
  rw [evaluate_components code hc.planarValid.1 M U w]
  apply congrArg List.prod
  apply List.map_congr_left
  intro c hm
  obtain ⟨g,hg,δ,ht,hp,hd⟩ := hc
  rw [MixedCode.encoding.decode_encode] at hd
  have heq := Option.some.inj hd
  subst code
  obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hm
  have hx : xs ∈ parts g := hxs
  have hv := extract_valid (withDomains (unaryTypes := 0) g δ) (withDomains_valid g hg δ) xs
  have htags := extract_tags (withDomains (unaryTypes := 0) g δ) δ (tags_withDomains g hg δ) xs
    (part_nodup g xs hx) (part_vertex_lt g xs hx)
  exact canonicalDomains_evaluate _ hv _ htags M U w

end PlanarHom.HomogeneousSourceOrientation
