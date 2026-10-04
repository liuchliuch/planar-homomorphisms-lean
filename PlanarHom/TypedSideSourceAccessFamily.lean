import PlanarHom.TypedSideSourceAccess
import PlanarHom.FiniteJointSourceAvailability

/-! Source access is derived from actual typed contextual reductions and an
explicit reduction from the retained base context to the original source P.
Contextual membership alone is never treated as an oracle algorithm. -/
noncomputable section
open Classical
namespace PlanarHom.TypedSideSourceAccess
open Complexity AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteContext TypedBipartiteSpectral FiniteLanguageAliases
variable {x y s n bt ut : ℕ}

@[simp] theorem zeroExtend_castAdd (N : Matrix (Fin x) (Fin x) ℝ) (i j : Fin x) :
    zeroExtendFin (y:=y) N (Fin.castAdd y i) (Fin.castAdd y j)=N i j :=
  zeroExtendFin_left N i j

theorem xFamily_algebraic (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) (N : Matrix (Fin x) (Fin x) ℝ)
    (hN : N∈xFamily F FB) : ∀i j,IsAlgebraic ℚ (N i j) := by
  intro i j
  simpa only [zeroExtend_castAdd] using
    hN.2.algebraic (Fin.castAdd y i) (Fin.castAdd y j)

/-- Ordinary evaluation of each actual X-family member reduces to the complete
original retained typed context. Companions and policies remain untouched. -/
def xFamily_typedReduction
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (L : RealLanguage (x+y) bt ut) (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀i,L.weights i=1) (hF : L.ContainsTypedMatrices B F FB)
    (N : Matrix (Fin x) (Fin x) ℝ) (hN : N∈xFamily F FB) :
    PromisePolyTimeTuringReduction
      (unitLanguage (fun _:Fin 1=>N) (fun _=>xFamily_algebraic F FB N hN)).problem
      (L.typedProblem (domains x y) B T) := by
  have access := canonicalSingleReduction (L.appendBinary (zeroExtendFin N) hN.2.algebraic)
    (appendOne B sameX) T hunit (Fin.last bt) (by simp [appendOne_aux,sameX])
    N (xFamily_algebraic F FB N hN)
    (by intro i j; simp only [appendBinary,appendOne_aux,zeroExtend_castAdd])
  exact access.trans (Classical.choice (hN.2.reduction L B T hunit hF))

/-- The source hypothesis is a real typed-context-to-P reduction, not assumed
availability or a hidden source algorithm. -/
def xFamily_singleSourceReduction
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (L : RealLanguage (x+y) bt ut) (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀i,L.weights i=1) (hF : L.ContainsTypedMatrices B F FB)
    (P : PromiseProblem) (source : PromisePolyTimeTuringReduction (L.typedProblem (domains x y) B T) P)
    (N : Matrix (Fin x) (Fin x) ℝ) (hN : N∈xFamily F FB) :
    PromisePolyTimeTuringReduction
      (unitLanguage (fun _:Fin 1=>N) (fun _=>xFamily_algebraic F FB N hN)).problem P :=
  (xFamily_typedReduction F FB L B T hunit hF N hN).trans source

/-- Finite joint X access follows by appending the literal zero-extensions
jointly, compiling the original graph once, and eliminating those new labels. -/
def xFamily_finiteTypedReduction
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (L : RealLanguage (x+y) bt ut) (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀i,L.weights i=1) (hF : L.ContainsTypedMatrices B F FB)
    (N : Fin n→Matrix (Fin x) (Fin x) ℝ) (hN : ∀l,N l∈xFamily F FB) :
    PromisePolyTimeTuringReduction
      (unitLanguage N (fun l=>xFamily_algebraic F FB (N l) (hN l))).problem
      (L.typedProblem (domains x y) B T) := by
  let A := fun l=>zeroExtendFin (y:=y) (N l)
  let AB := fun _:Fin n=>sameX
  let ha := fun l=>(hN l).2.algebraic
  have access := canonicalReduction (L.appendMatrices A ha) (appendFamily B AB) T hunit
    (Fin.natAdd bt) (by intro l; simp [appendFamily_new,AB,sameX])
    N (fun l=>xFamily_algebraic F FB (N l) (hN l))
    (by intro l i j; simp only [appendMatrices,appendFamily_new,A,zeroExtend_castAdd])
  have eliminate := typed_contextual_family_reduction (domains x y) F FB L B T hunit hF
    A AB (fun l=>(hN l).2)
  exact access.trans (Classical.choice eliminate)

/-- All finite mixed ordinary X languages reduce to the original source P. -/
theorem xFamily_finiteJointSource
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (L : RealLanguage (x+y) bt ut) (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀i,L.weights i=1) (hF : L.ContainsTypedMatrices B F FB)
    (P : PromiseProblem) (source : PromisePolyTimeTuringReduction (L.typedProblem (domains x y) B T) P) :
    FiniteJointSourceAvailable (xFamily F FB) (xFamily_algebraic F FB) P := by
  intro n N hN
  exact ⟨(xFamily_finiteTypedReduction F FB L B T hunit hF N hN).trans source⟩

end PlanarHom.TypedSideSourceAccess
