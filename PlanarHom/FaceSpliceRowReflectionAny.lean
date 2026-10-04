import PlanarHom.FaceSpliceRowReflection
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type} [Fintype E] [dD : DecidableEq (Dart E)] {G : MultiGraph V E}
 theorem face_eq_splices_of_rows_any (R : RotationRows G) (F : Equiv.Perm (Dart E))
    (ps : List (Dart E×Dart E)) (hn : (pairMarkers ps).Nodup)
    (hhost : ∀p∈ps,(G.dartPair (reversePerm E p.1)).1=(G.dartPair (reversePerm E p.2)).1)
    (huniq : ∀p∈ps,∀q∈ps,
      (G.dartPair (reversePerm E p.1)).1=(G.dartPair (reversePerm E q.1)).1 → p=q)
    (hsingle : ∀v,(¬∃p∈ps,(G.dartPair (reversePerm E p.1)).1=v) →
      ∀a∈R.row v,(R.row v).formPerm a=(F*reversePerm E) a)
    (hpaired : ∀p∈ps,∃xs ys : List (Dart E),
      R.row (G.dartPair (reversePerm E p.1)).1=
        (xs++[reversePerm E p.2])++(ys++[reversePerm E p.1]) ∧
      (∀a∈xs++[reversePerm E p.2],(F*reversePerm E) a=(xs++[reversePerm E p.2]).formPerm a) ∧
      (∀a∈ys++[reversePerm E p.1],(F*reversePerm E) a=(ys++[reversePerm E p.1]).formPerm a)) :
    R.facePerm=applyPairSplices F ps := by
  have hd : dD=(fun a b => @instDecidableEqProd E Bool (Classical.decEq E) instDecidableEqBool a b) := Subsingleton.elim _ _
  subst dD
  exact face_eq_splices_of_rows R F ps hn hhost huniq hsingle hpaired
end PlanarHom.FinitePermutationCycles
