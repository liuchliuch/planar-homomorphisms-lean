import PlanarHom.TypedYFamilyTransport
import PlanarHom.TypedSideSourceAccessFamily

/-! NEW genuine Y-side source access. The ordinary finite Y-matrix language
reduces to the actual retained typed context, using the complete recovered X-side
compiler and the verified color/domain transport. This does not assert a reduction
from that context to an ordinary cross-source oracle. -/
noncomputable section
namespace PlanarHom.TypedSideSourceAccess
open Complexity AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteContext
variable {x y s n bt ut : ℕ}

/-- Literal arbitrary-context transport of a finite ordinary Y-family. -/
def yFamily_finiteTypedReduction
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (L : RealLanguage (x+y) bt ut) (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀ i,L.weights i=1) (hF : L.ContainsTypedMatrices B F FB)
    (N : Fin n→Matrix (Fin y) (Fin y) ℝ) (hN : ∀ l,N l∈yFamily F FB) :
    PromisePolyTimeTuringReduction
      (unitLanguage N (fun l=>yFamily_algebraic F FB (N l) (hN l))).problem
      (L.typedProblem (domains x y) B T) := by
  let e := swapColors x y
  let V := L.coordinatePullback e
  let F' := fun l i j => F l (e i) (e j)
  let FB' := fun l a b => FB l (swapDomains a) (swapDomains b)
  let B' := fun l a b => B l (swapDomains a) (swapDomains b)
  let T' := fun l a => T l (swapDomains a)
  have hv : ∀ i,V.weights i=1 := fun i => hunit (e i)
  have hf : V.ContainsTypedMatrices B' F' FB' := by
    obtain ⟨index,hi⟩ := hF
    refine ⟨index,fun l => ⟨?_,?_⟩⟩
    · funext i j
      exact congrFun (congrFun (hi l).1 (e i)) (e j)
    · funext a b
      exact congrFun (congrFun (hi l).2 (swapDomains a)) (swapDomains b)
  have hn : ∀ l,N l∈xFamily F' FB' := by
    intro l
    rw [yFamily_eq_swapped_xFamily] at hN
    exact hN l
  have access := xFamily_finiteTypedReduction F' FB' V B' T' hv hf N hn
  have back := typedCoordinateReduction V L e swapDomains (domains x y) (domains y x)
    B' B T' T
    (fun d => (congrFun (swapColors_domains (x:=x) (y:=y)) d).symm)
    (fun _ _ _ h => h) (fun _ _ h => h)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  exact access.trans back

/-- Singleton form retains every unrelated source matrix and unary label. -/
def yFamily_typedReduction
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (L : RealLanguage (x+y) bt ut) (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀ i,L.weights i=1) (hF : L.ContainsTypedMatrices B F FB)
    (N : Matrix (Fin y) (Fin y) ℝ) (hN : N∈yFamily F FB) :
    PromisePolyTimeTuringReduction
      (unitLanguage (fun _:Fin 1=>N) (fun _=>yFamily_algebraic F FB N hN)).problem
      (L.typedProblem (domains x y) B T) :=
  yFamily_finiteTypedReduction F FB L B T hunit hF (fun _=>N) (fun _=>hN)

end PlanarHom.TypedSideSourceAccess
