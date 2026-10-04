import PlanarHom.PlanarityLRFaceComponents

/-! NEW finite dart connectivity from the actual DFS parent occurrences. -/
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityDepthFirstSearch

abbrev dartHost (g : MixedCode) (a : Dart (Fin g.edges.length)) : ℕ :=
  PlanarityRotationCode.host g (eraseDart a)

/-- The two primitive moves in the literal primal ribbon incidence graph. -/
def DartAdjacent (g : MixedCode) (a b : Dart (Fin g.edges.length)) : Prop :=
  b = reversePerm _ a ∨ dartHost g a = dartHost g b

theorem DartAdjacent.symm (g : MixedCode) : Symmetric (DartAdjacent g) := by
  intro a b h
  rcases h with rfl | h
  · left
    simp [reversePerm]
  · exact Or.inr h.symm

theorem dartHost_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (a : Dart (Fin g.edges.length)) : dartHost g a < g.vertices :=
  PlanarityRotationCode.host_valid g hg a.1.isLt

/-- An actual dart can reach a dart at its computed DFS root by crossing only
actual parent occurrences and moving between darts at the same vertex. -/
theorem dart_to_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (a : Dart (Fin g.edges.length)) :
    ∃ b : Dart (Fin g.edges.length), dartHost g b = componentRoot g (dartHost g a) ∧
      Relation.ReflTransGen (DartAdjacent g) a b := by
  suffices ∀ n (a : Dart (Fin g.edges.length)), height g (dartHost g a)=n →
      ∃ b : Dart (Fin g.edges.length), dartHost g b = componentRoot g (dartHost g a) ∧
        Relation.ReflTransGen (DartAdjacent g) a b from this _ a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro a hn
      have hv := dartHost_valid g hg a
      by_cases hz : height g (dartHost g a) = 0
      · exact ⟨a,(componentRoot_eq_self g hv hz).symm,.refl⟩
      · have hpos := Nat.pos_of_ne_zero hz
        have hp := parentEdge_tree g hg hv hpos
        let e := parentEdge g (dartHost g a)
        have he : e < g.edges.length := (of_decide_eq_true hp.1).1
        let p : Dart (Fin g.edges.length) := liftDart (PlanarityRotationCode.outward g e) he
        have hph : dartHost g p = parentVertex g (dartHost g a) := by
          simp only [dartHost,p,erase_liftDart,PlanarityRotationCode.host_outward]
          exact hp.2.2
        have hrh : dartHost g (reversePerm _ p) = dartHost g a := by
          simp only [dartHost,p,erase_reversePerm,erase_liftDart,PlanarityRotationCode.host_reverse_outward]
          exact hp.2.1
        have hlt : height g (dartHost g p) < n := by
          rw [hph,← hn]
          exact parentVertex_height_lt g hv hpos
        obtain ⟨b,hb,hr⟩ := ih _ hlt p rfl
        refine ⟨b,?_,?_⟩
        · rw [hb,hph]
          exact componentRoot_eq_of_desc g hv (Or.inr (parentVertex_ancestor g hv hpos))
        · have h₁ : DartAdjacent g a (reversePerm _ p) := Or.inr hrh.symm
          have h₂ : DartAdjacent g (reversePerm _ p) p := by left; simp [reversePerm]
          exact (Relation.ReflTransGen.single h₁).trans ((Relation.ReflTransGen.single h₂).trans hr)

/-- Equal computed roots imply connectivity of the actual dart incidence graph. -/
theorem dartConnected_of_componentRoot_eq (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (a b : Dart (Fin g.edges.length)) (hroot : componentRoot g (dartHost g a) = componentRoot g (dartHost g b)) :
    Relation.ReflTransGen (DartAdjacent g) a b := by
  obtain ⟨a',ha',haa'⟩ := dart_to_componentRoot g hg a
  obtain ⟨b',hb',hbb'⟩ := dart_to_componentRoot g hg b
  have hab : DartAdjacent g a' b' := Or.inr (ha'.trans (hroot.trans hb'.symm))
  exact haa'.trans ((Relation.ReflTransGen.single hab).trans
    (Relation.ReflTransGen.symmetric (DartAdjacent.symm g) hbb'))

end PlanarHom.PlanarityLRRealization
