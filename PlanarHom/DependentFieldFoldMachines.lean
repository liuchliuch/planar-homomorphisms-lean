import PlanarHom.DependentFieldCodecs
import PlanarHom.RestrictedListFoldMachines

/-! Genuine dependent folds with only same-parameter canonical operator calls. -/
namespace PlanarHom.DependentFieldFoldMachines
open Turing Complexity MachineComposition
open DependentFieldCodecs
variable {X : Type} {A : X → Type} (ex : BitEncoding X) (e : ∀ x, BitEncoding (A x))
variable (f : ∀ x, A x → A x → A x)

def operation (p : Σ x, A x × A x) : Σ x, A x := ⟨p.1, f p.1 p.2.1 p.2.2⟩

def fold (p : Σ x, A x × List (A x)) : Σ x, A x :=
  ⟨p.1,p.2.2.foldl (f p.1) p.2.1⟩

/-- The ordinary list-fold machine is reused pointwise. Its compiled body is one
uniform dependent operator; every trace call contains one unchanged x and two
canonical values in A x. Nothing is assumed about mismatched field words. -/
noncomputable def computer
    (body : TM2ComputableInPolyTime (DependentFieldCodecs.step ex e).toFinEncoding
      (DependentFieldCodecs.sigma ex e).toFinEncoding (operation f))
    (p : Polynomial ℕ)
    (sizeBound : ∀ (s : Σ x, A x × List (A x)) (i : ℕ), i ≤ s.2.2.length →
      ((DependentFieldCodecs.tagged ex e s.1).encode ((s.2.2.take i).foldl (f s.1) s.2.1)).length ≤
        p.eval ((DependentFieldCodecs.prepared ex e).encode s).length) :
    TM2ComputableInPolyTime (DependentFieldCodecs.prepared ex e).toFinEncoding
      (DependentFieldCodecs.sigma ex e).toFinEncoding (fold f) := by
  let time : Polynomial ℕ := (Polynomial.C 10*Polynomial.X+Polynomial.C 10)*(Polynomial.X+p+Polynomial.C 4)
  let g := body.toTM2ComputableAux
  let machine := ListFoldMachines.machine
  refine {
    tm := OracleSubstitution.machine machine g
    inputAlphabet := machine.core.inputAlphabet
    outputAlphabet := machine.core.outputAlphabet
    time := OracleSubstitution.timePolynomial machine time body.time
    outputsFun := ?_ }
  intro s
  rcases s with ⟨x,z,xs⟩
  apply Classical.choice
  obtain ⟨steps,cost,qs,hr,hcost,hgood⟩ := ListFoldMachines.run
    (ea := e x) (eb := DependentFieldCodecs.tagged ex e x) (f := f x) z xs
  have hN : ∀ k, ((machine.initial ((DependentFieldCodecs.prepared ex e).encode ⟨x,(z,xs)⟩)).stk k).length ≤
      ((DependentFieldCodecs.prepared ex e).encode ⟨x,(z,xs)⟩).length :=
    OracleReductionComposition.initial_length machine _
  have hc : cost ≤ time.eval ((DependentFieldCodecs.prepared ex e).encode ⟨x,(z,xs)⟩).length := by
    apply hcost.trans
    have h := ListFoldMachines.foldTime_bound_local (e x) (DependentFieldCodecs.tagged ex e x) (f x) z xs
      (p.eval ((DependentFieldCodecs.prepared ex e).encode ⟨x,(z,xs)⟩).length) (sizeBound ⟨x,(z,xs)⟩)
    simpa only [time, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
      ← DependentFieldCodecs.prepared_sameWords] using h
  obtain ⟨t,ht,he⟩ := OracleSubstitution.compiled_run_on_trace machine g hr body.time
    (fun q a hqa => by
      apply Classical.choice
      obtain ⟨v,hv⟩ := hgood (q,a) hqa
      have hq := congrArg Prod.fst hv
      have ha := congrArg Prod.snd hv
      dsimp only at hq ha
      subst q; subst a
      exact ⟨body.outputsFun ⟨x,v⟩⟩) _ hN
  refine ⟨{steps := t, evals_in_steps := ?_, steps_le_m := ?_}⟩
  · rw [OracleSubstitution.idle_initial, OracleSubstitution.idle_final] at he
    exact he
  · exact ht.trans (OracleReductionComposition.bound_polynomial machine time body.time
      ((DependentFieldCodecs.prepared ex e).encode ⟨x,(z,xs)⟩).length cost hc)

/-- Only the source's actual uniform operator and a proved prefix-size invariant
are used; framing preparation and operator rebracketing are actual FP programs. -/
theorem fp_fold
    (hf : FP (DependentFieldCodecs.pair ex e) (DependentFieldCodecs.sigma ex e) (operation f))
    (p : Polynomial ℕ)
    (sizeBound : ∀ (s : Σ x, A x × List (A x)) (i : ℕ), i ≤ s.2.2.length →
      ((DependentFieldCodecs.tagged ex e s.1).encode ((s.2.2.take i).foldl (f s.1) s.2.1)).length ≤
        p.eval ((DependentFieldCodecs.prepared ex e).encode s).length) :
    FP (DependentFieldCodecs.input ex e) (DependentFieldCodecs.sigma ex e) (fold f) := by
  obtain ⟨body⟩ := (DependentFieldCodecs.fp_step_to_pair ex e).comp hf
  exact (DependentFieldCodecs.fp_prepare ex e).comp ⟨computer ex e f body p sizeBound⟩

end PlanarHom.DependentFieldFoldMachines
