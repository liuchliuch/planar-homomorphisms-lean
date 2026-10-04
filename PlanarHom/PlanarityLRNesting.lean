import PlanarHom.PlanarityLRConstraints
import Mathlib.Data.List.Sort

/-! NEW deterministic nesting order and side extension for literal LR rows.
Only a computed aligned LR assignment can later justify planar realization;
these definitions themselves are total on every raw graph and bit list. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityLRConstraints

/-- Choose a highest return target, retaining an actual original occurrence. -/
def maximumReturn (g : MixedCode) : List ℕ → Option ℕ
  | [] => none
  | e::es => match maximumReturn g es with
    | none => some e
    | some b => some (if targetHeight g b ≤ targetHeight g e then e else b)

theorem maximumReturn_none (g : MixedCode) (es : List ℕ) : maximumReturn g es = none ↔ es = [] := by
  cases es with
  | nil => simp [maximumReturn]
  | cons e es => simp only [maximumReturn]; cases maximumReturn g es <;> simp

theorem maximumReturn_spec (g : MixedCode) (es : List ℕ) {e : ℕ} (he : maximumReturn g es = some e) :
    e ∈ es ∧ ∀ b ∈ es, targetHeight g b ≤ targetHeight g e := by
  induction es generalizing e with
  | nil => simp [maximumReturn] at he
  | cons a es ih =>
    cases hb : maximumReturn g es with
    | none =>
      have hes := (maximumReturn_none g es).mp hb
      subst es
      simp [maximumReturn] at he
      subst e
      simp
    | some b =>
      have hs := ih hb
      simp only [maximumReturn,hb] at he
      split_ifs at he with hba
      · have heq := Option.some.inj he
        subst e
        refine ⟨List.mem_cons_self ..,?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact le_rfl
        · exact (hs.2 c hc).trans hba
      · have heq := Option.some.inj he
        subst e
        refine ⟨List.mem_cons_of_mem _ hs.1,?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · omega
        · exact hs.2 c hc

/-- Tree edges inherit the side of a highest-return fundamental cycle. -/
def edgeSide (g : MixedCode) (bits : List Bool) (e : ℕ) : Bool :=
  match maximumReturn g (returns g e) with
  | none => true
  | some b => bitSide bits b

theorem edgeSide_witness (g : MixedCode) (bits : List Bool) (e : ℕ)
    (h : returns g e ≠ []) :
    ∃ b ∈ returns g e, edgeSide g bits e = bitSide bits b ∧
      ∀ c ∈ returns g e, targetHeight g c ≤ targetHeight g b := by
  cases hb : maximumReturn g (returns g e) with
  | none => exact (h ((maximumReturn_none g _).mp hb)).elim
  | some b =>
    have hs := maximumReturn_spec g _ hb
    exact ⟨b,hs.1,by simp [edgeSide,hb],hs.2⟩

theorem edgeSide_back (g : MixedCode) (bits : List Bool) {e : ℕ} (he : isBack g e = true) :
    edgeSide g bits e = bitSide bits e := by
  have ht : isTree g e = false := (of_decide_eq_true he).2.1
  simp [edgeSide,returns,ht,he,maximumReturn]

/-- A constrained return lies on the extended side of its outgoing tree edge,
since a highest return belongs to the same monochromatic fork group. -/
theorem edgeSide_of_fork_return (g : MixedCode) (bits : List Bool)
    (hLR : LRCondition g (bitSide bits)) {v e₁ e₂ b : ℕ}
    (hv : v < g.vertices) (hh : 0 < height g v)
    (he₁ : e₁ ∈ outgoing g v) (he₂ : e₂ ∈ outgoing g v) (hne : e₂ ≠ e₁)
    (hb : b ∈ (forkBlock g e₁ e₂).1) : edgeSide g bits e₁ = bitSide bits b := by
  have hbr := (List.mem_filter.mp hb).1
  have hcut : lowpoint g e₂ < targetHeight g b := of_decide_eq_true (List.mem_filter.mp hb).2
  obtain ⟨c,hc,hside,hmax⟩ := edgeSide_witness g bits e₁ (fun he => by simpa [he] using hbr)
  have hcg : c ∈ (forkBlock g e₁ e₂).1 :=
    List.mem_filter.mpr ⟨hc,decide_eq_true (hcut.trans_le (hmax b hbr))⟩
  rw [hside]
  exact (hLR v hv hh e₁ he₁ e₂ he₂ hne).1 c hcg b hb

/-- A chordal branch has a return strictly above its own lowpoint. -/
def chordal (g : MixedCode) (e : ℕ) : Bool :=
  (returns g e).any (fun b => decide (lowpoint g e < targetHeight g b))

def nestingDepth (g : MixedCode) (e : ℕ) : ℕ :=
  2*lowpoint g e + if chordal g e then 1 else 0

/-- Original occurrence index is a deterministic tie-breaker. -/
def nestingLE (g : MixedCode) (e f : ℕ) : Bool :=
  decide (nestingDepth g e < nestingDepth g f ∨ nestingDepth g e = nestingDepth g f ∧ e ≤ f)

theorem nestingLE_trans (g : MixedCode) (a b c : ℕ)
    (hab : nestingLE g a b = true) (hbc : nestingLE g b c = true) : nestingLE g a c = true := by
  simp only [nestingLE,decide_eq_true_eq] at *
  omega

theorem nestingLE_total (g : MixedCode) (a b : ℕ) : (nestingLE g a b || nestingLE g b a) = true := by
  simp only [nestingLE,Bool.or_eq_true,decide_eq_true_eq]
  omega

theorem nestingLE_antisymm (g : MixedCode) (a b : ℕ)
    (hab : nestingLE g a b = true) (hba : nestingLE g b a = true) : a = b := by
  simp only [nestingLE,decide_eq_true_eq] at *
  omega

def nestingOutgoing (g : MixedCode) (v : ℕ) : List ℕ := (outgoing g v).mergeSort (nestingLE g)

/-- Flip-reverse left edges before the right edges, preserving every occurrence. -/
def orderedOutgoing (g : MixedCode) (bits : List Bool) (v : ℕ) : List ℕ :=
  ((nestingOutgoing g v).filter (fun e => !(edgeSide g bits e))).reverse ++
    (nestingOutgoing g v).filter (edgeSide g bits)

theorem nestingOutgoing_sorted (g : MixedCode) (v : ℕ) :
    (nestingOutgoing g v).Pairwise (fun a b => nestingLE g a b = true) :=
  List.sorted_mergeSort (nestingLE_trans g) (nestingLE_total g) _

theorem nestingOutgoing_perm (g : MixedCode) (v : ℕ) : (nestingOutgoing g v).Perm (outgoing g v) :=
  List.mergeSort_perm _ _

theorem orderedOutgoing_perm (g : MixedCode) (bits : List Bool) (v : ℕ) :
    (orderedOutgoing g bits v).Perm (outgoing g v) := by
  unfold orderedOutgoing
  apply List.Perm.trans ((List.reverse_perm _).append (List.Perm.refl _))
  have hp := List.filter_append_perm (fun e => !(edgeSide g bits e)) (nestingOutgoing g v)
  simp only [Bool.not_not] at hp
  exact hp.trans (nestingOutgoing_perm g v)

@[simp] theorem mem_orderedOutgoing (g : MixedCode) (bits : List Bool) (v e : ℕ) :
    e ∈ orderedOutgoing g bits v ↔ e ∈ outgoing g v := (orderedOutgoing_perm g bits v).mem_iff

theorem orderedOutgoing_nodup (g : MixedCode) (bits : List Bool) (v : ℕ) :
    (orderedOutgoing g bits v).Nodup := by
  apply (orderedOutgoing_perm g bits v).symm.nodup
  exact List.nodup_range.filter _

@[simp] theorem orderedOutgoing_length (g : MixedCode) (bits : List Bool) (v : ℕ) :
    (orderedOutgoing g bits v).length = (outgoing g v).length := (orderedOutgoing_perm g bits v).length_eq

end PlanarHom.PlanarityLRDirect
