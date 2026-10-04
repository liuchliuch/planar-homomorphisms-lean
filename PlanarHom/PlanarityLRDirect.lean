import PlanarHom.PlanarityRotationCode

/-! NEW deterministic LR row construction. The definitions preserve literal
dart identities and use DFS path words to order incoming back-edge events.
Incidence/permutation and faithful-realization proofs are separate below. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityLRConstraints
open PlanarityRotationCode

/-- Lexicographic tree-branch word in the LR-ordered outgoing rows. -/
def treeWord (g : MixedCode) (bits : List Bool) (v : ℕ) : List ℕ :=
  ((rootPath g v).drop 1).map (fun w =>
    (orderedOutgoing g bits (parentVertex g w)).idxOf (parentEdge g w))

def backWord (g : MixedCode) (bits : List Bool) (b : ℕ) : List ℕ :=
  treeWord g bits (source g b) ++ [(orderedOutgoing g bits (source g b)).idxOf b]

def eventLE (g : MixedCode) (bits : List Bool) (a b : ℕ) : Bool :=
  (backWord g bits a).lex (backWord g bits b) (fun x y => decide (x < y)) ||
    decide (backWord g bits a = backWord g bits b ∧ a ≤ b)

def backEvents (g : MixedCode) (bits : List Bool) : List ℕ :=
  ((List.range g.edges.length).filter (isBack g)).mergeSort (eventLE g bits)

/-- Incoming back darts are inserted before or after their literal first tree
branch; each side uses reverse DFS-event order as in the row-insertion algorithm. -/
def incoming (g : MixedCode) (bits : List Bool) (e : ℕ) (side : Bool) : List Dart :=
  (((backEvents g bits).filter (fun b => decide (branchEdge g b = e ∧ bitSide bits b = side))).reverse).map
    (fun b => reverse (outward g b))

def edgeBlock (g : MixedCode) (bits : List Bool) (e : ℕ) : List Dart :=
  incoming g bits e false ++ [outward g e] ++ incoming g bits e true

def parentRow (g : MixedCode) (v : ℕ) : List Dart :=
  if height g v = 0 then [] else [reverse (outward g (parentEdge g v))]

/-- Loops occupy consecutive local ports and are never merged with another occurrence. -/
def loopRow (g : MixedCode) (v : ℕ) : List Dart :=
  ((List.range g.edges.length).filter (fun e => decide ((edge g e).1 = (edge g e).2.1 ∧ (edge g e).1 = v))).flatMap
    (fun e => [(e,true),(e,false)])

def directRow (g : MixedCode) (bits : List Bool) (v : ℕ) : List Dart :=
  parentRow g v ++ (orderedOutgoing g bits v).flatMap (edgeBlock g bits) ++ loopRow g v

/-- Total cyclic row lookup. Empty rows keep the supplied dart; a missing dart
in a nonempty row follows the total modulo-index convention. -/
def rowNext (row : List Dart) (a : Dart) : Dart :=
  row.getD ((row.idxOf a + 1) % row.length) a

def directRotation (g : MixedCode) (bits : List Bool) (a : Dart) : Dart :=
  rowNext (directRow g bits (host g a)) a

def faceStep (g : MixedCode) (bits : List Bool) (a : Dart) : Dart :=
  directRotation g bits (reverse a)

theorem backEvents_perm (g : MixedCode) (bits : List Bool) :
    (backEvents g bits).Perm ((List.range g.edges.length).filter (isBack g)) :=
  List.mergeSort_perm _ _

@[simp] theorem mem_backEvents (g : MixedCode) (bits : List Bool) (b : ℕ) :
    b ∈ backEvents g bits ↔ isBack g b = true := by
  rw [(backEvents_perm g bits).mem_iff,List.mem_filter,List.mem_range]
  exact ⟨And.right,fun h => ⟨(of_decide_eq_true h).1,h⟩⟩

theorem backEvents_nodup (g : MixedCode) (bits : List Bool) : (backEvents g bits).Nodup :=
  (backEvents_perm g bits).symm.nodup (List.nodup_range.filter _)

theorem mem_incoming (g : MixedCode) (bits : List Bool) (e : ℕ) (side : Bool) (a : Dart) :
    a ∈ incoming g bits e side ↔
      ∃ b, isBack g b = true ∧ branchEdge g b = e ∧ bitSide bits b = side ∧ reverse (outward g b) = a := by
  simp only [incoming,List.mem_map,List.mem_reverse,List.mem_filter,mem_backEvents,decide_eq_true_eq]
  constructor
  · rintro ⟨b,⟨hb,he,hs⟩,ha⟩
    exact ⟨b,hb,he,hs,ha⟩
  · rintro ⟨b,hb,he,hs,ha⟩
    exact ⟨b,⟨hb,he,hs⟩,ha⟩

end PlanarHom.PlanarityLRDirect
