import PlanarHom.OracleReductionComposition

/-! Concrete identity reductions and regression instances for the compiler API. -/

namespace PlanarHom.Complexity

open Turing Polynomial PlanarHom.MachineComposition

/-- Promised reflexivity uses one actual oracle query. Its polynomial output
bound is required only on promised inputs, and every extension of the oracle
is handled by the same machine. -/
noncomputable def PromisePolyTimeTuringReduction.refl_of_output_bound
    (P : PromiseProblem) (p : Polynomial ℕ)
    (sizeBound : ∀ x, P.valid x → (P.value x).length ≤ p.eval x.length) :
    PromisePolyTimeTuringReduction P P where
  machine := directQueryMachine
  time := 2 + X + p
  computes oracle ho x hx := by
    have he : oracle x = P.value x := ho x hx
    refine ⟨2,2+x.length+(P.value x).length,[(x,P.value x)],?_,?_,?_⟩
    · simpa only [he] using directQueryMachine_run oracle x
    · simpa using Nat.add_le_add_left (sizeBound x hx) (2+x.length)
    · intro q a hqa
      have hpair : (q,a) = (x,P.value x) := List.mem_singleton.mp hqa
      have hq : q = x := congrArg Prod.fst hpair
      simpa only [hq] using hx

/-- A genuine polynomial-time computer supplies its own proved output-length
bound, so its function admits a concrete reflexive oracle reduction. -/
noncomputable def PolyTimeTuringReduction.refl_of_computer {f : Bits → Bits}
    (computer : TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding
      BitEncoding.bits.toFinEncoding f) : PolyTimeTuringReduction f f :=
  directQueryReduction f (outputLengthPolynomial computer)
    (fun x => encoded_output_length_le computer x)

theorem TuringReduces.refl_of_fp {f : Bits → Bits}
    (h : FP BitEncoding.bits BitEncoding.bits f) : TuringReduces f f := by
  obtain ⟨computer⟩ := h
  exact ⟨PolyTimeTuringReduction.refl_of_computer computer⟩

/-- A regression instance exercises composition and elimination on the concrete
single-stack query machine, whose query and answer stacks are the same stack. -/
theorem identity_compiler_regression : FP BitEncoding.bits BitEncoding.bits id := by
  let r := directQueryReduction id X (by intro x; simp)
  exact (r.trans r).fp (fp_id BitEncoding.bits)

/-- Arbitrary predicates remain promises when the concrete promised identity
reduction is composed with itself, preserving the all-extensions quantifier. -/
noncomputable def promise_identity_compiler_regression (valid : Bits → Prop) :
    PromisePolyTimeTuringReduction ⟨valid,id⟩ ⟨valid,id⟩ := by
  let r := PromisePolyTimeTuringReduction.refl_of_output_bound ⟨valid,id⟩ X
    (by intro x hx; simp)
  exact r.trans r

end PlanarHom.Complexity
