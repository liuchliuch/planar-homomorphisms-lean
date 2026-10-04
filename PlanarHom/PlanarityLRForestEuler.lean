import PlanarHom.PlanarityLRForestFaceCount

/-! NEW subtraction-free Euler identity from actual forest size and the proved
single-contour noncrossing face count. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization
open MultiGraph MultiGraph.Kasteleyn FinitePermutationCycles

 def partitionEdgeEquiv {E : Type*} (selected : E → Bool) :
    E ≃ {e // selected e=false} ⊕ {e // selected e=true} where
  toFun e := if h : selected e=true then .inr ⟨e,h⟩ else .inl ⟨e,Bool.eq_false_iff.mpr h⟩
  invFun | .inl e => e.val | .inr e => e.val
  left_inv e := by dsimp only; split_ifs <;> rfl
  right_inv e := by
    rcases e with ⟨e,he⟩ | ⟨e,he⟩
    · simp only [he,Bool.false_eq_true,↓reduceDIte]
    · simp only [he,↓reduceDIte]

 theorem edge_card_partition {E : Type*} [Finite E] (selected : E → Bool) :
    Nat.card E=Nat.card {e // selected e=false}+Nat.card {e // selected e=true} := by
  rw [Nat.card_congr (partitionEdgeEquiv selected),Nat.card_sum]

 theorem euler_of_single_forest_contour {V E K : Type*} [Finite V] [Finite E] [DecidableEq E] [LinearOrder K]
    (R : Equiv.Perm (Dart E)) (selected : E → Bool) (a : Dart E)
    (hsingle : ∀x,Equiv.Perm.SameCycle ((partialReverse E selected).trans R) a x)
    (htree : Nat.card {e // selected e=true}+1=Nat.card V)
    (key : Dart {e // selected e=false} → K)
    (hsort : (visibleContourWord R selected a).Pairwise (fun x y => key x<key y))
    (horder : ∀e f : {e // selected e=false}, e≠f →
      PortNoncrossing (key (e,true)) (key (e,false)) (key (f,true)) (key (f,false))) :
    Nat.card V+count ((reversePerm E).trans R)=Nat.card E+2 := by
  have hcard := edge_card_partition selected
  by_cases hv : Nonempty {e // selected e=false}
  · letI := hv
    have hf := count_faces_of_key_noncrossing R selected a hsingle key hsort horder
    omega
  · have hall : ∀e,selected e=true := by
      intro e
      cases h : selected e
      · exact (hv ⟨⟨e,h⟩⟩).elim
      · rfl
    letI : IsEmpty {e // selected e=false} := ⟨fun e => hv ⟨e⟩⟩
    have hz : Nat.card {e // selected e=false}=0  := Nat.card_eq_zero.mpr (Or.inl inferInstance)
    have hf := count_faces_tree_only R selected a hsingle hall
    omega

end PlanarHom.PlanarityLRRealization
