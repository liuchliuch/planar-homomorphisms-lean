import PlanarHom.TM2SingleTapeLoading
import PlanarHom.NondeterministicBlockSimulation

/-! # Ordinary-transition blocks for input loading and output checking -/
namespace PlanarHom.TM2SingleTapeLoading
open Turing SingleTapeNondeterministic NondeterministicComputationTree
  NondeterministicBlockSimulation

section Loader
variable {K : Type} {Γ : K → Type} [DecidableEq K]
  (k : K) (encode : Bool → Γ k)
  {D : Type} (view : D → NodeView D)
  (embed : Control LoaderState × Tape (Alphabet K Γ) → D)
  (ordinary : ∀ q t, q ≠ .done →
    view (embed (.run q, t)) = .ordinary (embed (loaderStep k encode (.run q, t))))
include ordinary

theorem loader_scan_run (xs : List Bool) (left : List (Alphabet K Γ)) :
    OrdinaryRun view xs.length
      (embed (.run (.scan true), Tape.mk₂ left (xs.map .raw)))
      (embed (.run (.scan true),
        Tape.mk₂ (xs.reverse.map (converted k encode) ++ left) [])) := by
  induction xs generalizing left with
  | nil => exact .nil _
  | cons b xs ih =>
    simp only [List.length_cons, List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append]
    apply OrdinaryRun.cons (ordinary (.scan true) _ (by decide))
    rw [loader_raw]
    exact ih _

theorem loader_finish_run (xs : List Bool) (h : xs ≠ []) :
    OrdinaryRun view 2
      (embed (.run (.scan true), Tape.mk₂ (xs.reverse.map (converted k encode)) []))
      (embed (.run .done, loaded k encode xs)) := by
  let t : Tape (Alphabet K Γ) := Tape.mk₂ (xs.reverse.map (converted k encode)) []
  have hfirst : loaderStep k encode (.run (.scan true), t) =
      (.run .mark, t.move .left) := rfl
  have hlast : loaderStep k encode (.run .mark, t.move .left) =
      (.run .done, loaded k encode xs) := by
    have he := finish_nonempty k encode xs h
    change loaderStep k encode (loaderStep k encode (.run (.scan true), t)) = _ at he
    rwa [hfirst] at he
  apply OrdinaryRun.cons (ordinary (.scan true) t (by decide))
  rw [hfirst]
  apply OrdinaryRun.cons (ordinary .mark (t.move .left) (by decide))
  rw [hlast]
  exact .nil _

/-- Loading is a block of actual ordinary tree edges. The enclosing target may
identify `.done` with an arbitrary simulation continuation. -/
theorem loader_run (xs : List Bool) :
    OrdinaryRun view (if xs = [] then 1 else xs.length + 2)
      (embed (.run (.scan false), Tape.mk₁ (xs.map .raw)))
      (embed (.run .done, loaded k encode xs)) := by
  cases xs with
  | nil =>
    apply OrdinaryRun.cons (ordinary (.scan false) _ (by decide))
    exact .nil _
  | cons b xs =>
    simp only [reduceCtorEq, if_false, List.length_cons]
    have hr := loader_scan_run k encode view embed ordinary xs [converted k encode b]
    have hp : xs.reverse.map (converted k encode) ++ [converted k encode b] =
        (b :: xs).reverse.map (converted k encode) := by simp
    rw [hp] at hr
    have ht := hr.trans (loader_finish_run k encode view embed ordinary (b :: xs) (by simp))
    rw [show xs.length + 1 + 2 = (xs.length + 2) + 1 by omega]
    apply OrdinaryRun.cons (ordinary (.scan false) _ (by decide))
    change OrdinaryRun view (xs.length + 2)
      (embed (.run (.scan true), Tape.mk₂ [converted k encode b] (xs.map .raw))) _
    exact ht

end Loader

variable {K : Type} {Γ : K → Type} [DecidableEq K]
  (k : K) {D : Type} (view : D → NodeView D)

theorem checker_run (aTrue : Γ k) [DecidableEq (Γ k)]
    (embed : Control CheckerState × Tape (Alphabet K Γ) → D)
    (ordinary : ∀ q t,
      view (embed (.run q, t)) = .ordinary (embed (checkerStep k aTrue (.run q, t))))
    (L : ListBlank (∀ j, Option (Γ j))) (S : List (Γ k))
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) :
    OrdinaryRun view 2 (embed (.run .first, represented L))
      (embed (if S = [aTrue] then .accept else .reject, (represented L).move .left)) := by
  let t := represented L
  let flag := match t.head with
    | Alphabet.raw _ => false
    | Alphabet.sim a => decide (a.2 k = some aTrue)
  have hfirst : checkerStep k aTrue (.run .first, t) =
      (.run (.second flag), t.move .left) := by
    simp only [checkerStep, checkerAction, execute, Tape.write_self]
    rfl
  have hlast : checkerStep k aTrue (.run (.second flag), t.move .left) =
      (if S = [aTrue] then .accept else .reject, t.move .left) := by
    have he := checker_exact k aTrue L S hL
    change checkerStep k aTrue (checkerStep k aTrue (.run .first, t)) = _ at he
    rwa [hfirst] at he
  apply OrdinaryRun.cons (ordinary .first t)
  rw [hfirst]
  apply OrdinaryRun.cons (ordinary (.second flag) (t.move .left))
  rw [hlast]
  exact .nil _

end PlanarHom.TM2SingleTapeLoading
