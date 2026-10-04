import PlanarHom.PrescribedDomainAliasReductions
import PlanarHom.FiniteLanguageJointReductions

/-! Actual alias machines remove temporary binary/unary labels while retaining
all original labels and a complete appended finite family. -/
noncomputable section
namespace PlanarHom.FiniteLanguageAliases

def skipAuxFamily (b n : ℕ) : Fin (b+n)→Fin (b+1+n) :=
  Fin.addCases (fun i=>Fin.castAdd n (Fin.castAdd 1 i)) (fun j=>Fin.natAdd (b+1) j)

theorem appendFamily_skipAux {α : Type} {b n : ℕ} (M : Fin b→α) (A : α) (N : Fin n→α) :
    appendFamily (appendOne M A) N ∘ skipAuxFamily b n=appendFamily M N := by
  funext i
  refine Fin.addCases (fun l=>?_) (fun j=>?_) i
  · simp only [Function.comp_apply,skipAuxFamily,Fin.addCases_left,appendFamily,Fin.addCases_left]
    exact appendOne_old M A l
  · simp only [Function.comp_apply,skipAuxFamily,Fin.addCases_right,appendFamily,Fin.addCases_right]

end PlanarHom.FiniteLanguageAliases
namespace PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLanguageAliases
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {bt ut n m d dimension : ℕ}

def skipAuxFamiliesReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix C C K) (A : Matrix C C K) (N : Fin n→Matrix C C K)
    (U : Fin ut→C→K) (a : C→K) (V : Fin m→C→K) (w : C→K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (appendFamily M N) (appendFamily U V) w)
      (evaluationProblem basis (appendFamily (appendOne M A) N) (appendFamily (appendOne U a) V) w) := by
  have first : PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendFamily M N) (appendFamily U V) w)
      (evaluationProblem basis (appendFamily (appendOne M A) N) (appendFamily U V) w) := by
    simpa only [appendFamily_skipAux] using binaryRelabelReduction basis (skipAuxFamily bt n)
      (appendFamily (appendOne M A) N) (appendFamily U V) w
  have second : PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendFamily (appendOne M A) N) (appendFamily U V) w)
      (evaluationProblem basis (appendFamily (appendOne M A) N) (appendFamily (appendOne U a) V) w) := by
    simpa only [appendFamily_skipAux] using unaryRelabelReduction basis (skipAuxFamily ut m)
      (appendFamily (appendOne M A) N) (appendFamily (appendOne U a) V) w
  exact first.trans second

def domainSkipAuxFamiliesReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix C C K) (A : Matrix C C K) (N : Fin n→Matrix C C K)
    (U : Fin ut→C→K) (a : C→K) (V : Fin m→C→K) (w : C→K)
    (D : Fin d→Set C) (B : Fin bt→Fin d→Fin d→Prop) (BA : Fin d→Fin d→Prop)
    (BN : Fin n→Fin d→Fin d→Prop) (T : Fin ut→Fin d→Prop) (Ta : Fin d→Prop) (TV : Fin m→Fin d→Prop) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendFamily M N) (appendFamily U V) w D (appendFamily B BN) (appendFamily T TV))
      (domainEvaluationProblem basis (appendFamily (appendOne M A) N) (appendFamily (appendOne U a) V) w
        D (appendFamily (appendOne B BA) BN) (appendFamily (appendOne T Ta) TV)) := by
  have hb : ∀i x y,appendFamily B BN i x y→appendFamily (appendOne B BA) BN (skipAuxFamily bt n i) x y := by
    intro i x y h
    exact (congrFun (congrFun (congrFun (appendFamily_skipAux B BA BN) i) x) y).mpr h
  have ht : ∀i x,appendFamily T TV i x→appendFamily (appendOne T Ta) TV (skipAuxFamily ut m i) x := by
    intro i x h
    exact (congrFun (congrFun (appendFamily_skipAux T Ta TV) i) x).mpr h
  have first := domainBinaryRelabelReduction basis (skipAuxFamily bt n)
    (appendFamily (appendOne M A) N) (appendFamily U V) w D
    (appendFamily B BN) (appendFamily (appendOne B BA) BN) (appendFamily T TV) hb
  have second := domainUnaryRelabelReduction basis (skipAuxFamily ut m)
    (appendFamily (appendOne M A) N) (appendFamily (appendOne U a) V) w D
    (appendFamily (appendOne B BA) BN) (appendFamily T TV) (appendFamily (appendOne T Ta) TV) ht
  simp only [appendFamily_skipAux] at first second
  exact first.trans second

end PlanarHom.Complexity.MixedCode
