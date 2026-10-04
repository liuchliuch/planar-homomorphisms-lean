import PlanarHom.OccurrenceMatchingCycleDecompositionData
import PlanarHom.OccurrenceMatchingCycleRatio

/-! NEW telescoping of literal matching signs over an exact disjoint cycle family. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
open Kasteleyn

private theorem telescope {A : Type*} [CommMonoid A] (n : ℕ)
    (s : Fin (n+1) → A) (f : Fin n → A)
    (h : ∀i,s i.castSucc=s i.succ*f i) : s 0=s (Fin.last n)*∏i,f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := ih (fun i => s i.succ) (fun i => f i.succ)
      (fun i => by simpa only [Fin.succ_castSucc] using h i.succ)
    rw [Fin.prod_univ_succ]
    calc
      s 0 = s (Fin.succ 0)*f 0 := by simpa using h 0
      _ = (s (Fin.last n).succ * ∏i:Fin n,f i.succ)*f 0 := congrArg (fun z => z*f 0) ht
      _ = _ := by simp only [Fin.succ_last]; ac_rfl

variable {V E : Type*} [Fintype V] [Fintype E] [LinearOrder V]
variable {G : MultiGraph V E} {M N : Finset E} {n : ℕ}

theorem MatchingCycleDecomposition.matchingPfaffianSign_product
    (d : MatchingCycleDecomposition G M N n) (orientation : E → Bool) :
    G.matchingPfaffianSign (R := ℤ) orientation M =
      G.matchingPfaffianSign orientation N *
        ∏ i, (-boundarySign orientation (d.family.cycle i).cycleDarts) := by
  have h := telescope n (fun i => G.matchingPfaffianSign (R:=ℤ) orientation (d.states i))
    (fun i => -boundarySign orientation (d.family.cycle i).cycleDarts) (fun i => by
      simpa only [d.flip_cycle i] using (d.flips i).matchingPfaffianSign_ratio orientation)
  simpa only [d.states_first,d.states_last] using h

end PlanarHom.MultiGraph
