import PlanarHom.PlanarityLRContourPermutation
import PlanarHom.RadialPottsAssemblyCornerOrder

/-! Explicit positions of every original dart in its computed cyclic row. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type} {G : MultiGraph V E} [DecidableEq (Dart E)]

namespace RotationRows

def rowIndex (R : PlanarityLRRealization.RotationRows G) (a : Dart E) :
    Fin (R.row (G.dartPair a).1).length :=
  ⟨(R.row (G.dartPair a).1).idxOf a,List.idxOf_lt_length_iff.mpr ((R.mem _ a).mpr rfl)⟩

@[simp] theorem row_get_index (R : PlanarityLRRealization.RotationRows G) (a : Dart E) :
    (R.row (G.dartPair a).1).get (rowIndex R a)=a := by
  have hi : (R.row (G.dartPair a).1).idxOf a<(R.row (G.dartPair a).1).length :=
    List.idxOf_lt_length_iff.mpr ((R.mem _ a).mpr rfl)
  change (R.row (G.dartPair a).1)[(R.row (G.dartPair a).1).idxOf a]=a
  exact eq_of_beq (List.findIdx_getElem (p:=fun b=>b==a) (xs:=R.row (G.dartPair a).1) (w:=hi))

theorem next_val {n : ℕ} (i : Fin n) : (CornerOrder.next i).val=(i.val+1)%n := by
  unfold CornerOrder.next
  split_ifs with h
  · dsimp
    exact (Nat.mod_eq_of_lt h).symm
  · have hi : i.val+1=n := by have := i.isLt; omega
    simp [hi]

@[simp] theorem row_get_next (R : PlanarityLRRealization.RotationRows G) (a : Dart E) :
    (R.row (G.dartPair a).1).get (CornerOrder.next (rowIndex R a))=R.rotation a := by
  let xs := R.row (G.dartPair a).1
  let i := rowIndex R a
  have hi : xs[i.val]=a := row_get_index R a
  change xs.get (CornerOrder.next i)=xs.formPerm a
  rw [← hi,List.formPerm_apply_getElem xs (R.nodup _) i.val i.isLt]
  simp only [List.get_eq_getElem]
  congr 1
  exact next_val i

def wireIndex {k : ℕ} (R : PlanarityLRRealization.RotationRows G) (w : Dart E×Fin k) :
    (v : V) × (Fin (R.row v).length×Fin k) :=
  ⟨(G.dartPair w.1).1,(rowIndex R w.1,w.2)⟩

def wireUnindex {k : ℕ} (R : PlanarityLRRealization.RotationRows G) :
    ((v : V) × (Fin (R.row v).length×Fin k))→Dart E×Fin k
  | ⟨v,(i,a)⟩ => ((R.row v).get i,a)

@[simp] theorem wireUnindex_wireIndex {k : ℕ} (R : PlanarityLRRealization.RotationRows G)
    (w : Dart E×Fin k) : wireUnindex R (wireIndex R w)=w := by
  rcases w with ⟨a,j⟩
  change ((R.row (G.dartPair a).1).get (rowIndex R a),j)=(a,j)
  rw [row_get_index]

theorem wireIndex_injective {k : ℕ} (R : PlanarityLRRealization.RotationRows G) :
    Function.Injective (wireIndex (k:=k) R) := by
  intro w z h
  have hh := congrArg (wireUnindex R) h
  simpa using hh

end RotationRows
end PlanarHom.RadialPottsAssemblyGeometry
