import PlanarHom.DomainParameterizedPowerReduction

open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLanguageAliases

private def mixedLoop : MixedCode :=
  ⟨2,[(0,0,2),(0,1,1),(1,0,2)],[(0,3),(0,3),(1,1)]⟩

private theorem mixedLoop_valid : mixedLoop.Valid 3 4 := by
  simp [MixedCode.Valid,mixedLoop]

example : (mixedLoop.stretchLabel 2 2 2).vertices=6 := by decide
example : (mixedLoop.stretchLabel 2 2 2).edges=
    [(0,2,2),(2,3,2),(3,0,2),(1,4,2),(4,5,2),(5,0,2),(0,1,1)] := by decide
example : (mixedLoop.stretchLabel 2 2 2).unaries=mixedLoop.unaries := rfl
example : (mixedLoop.stretchLabel 2 2 0).edges=[(0,0,2),(1,0,2),(0,1,1)] := by decide
example : (mixedLoop.stretchLabel 9 9 5)=mixedLoop :=
  ParameterizedPowerReduction.query_of_noSelected _ _ _ (by simp [mixedLoop])

example (M : Fin 2→Matrix (Fin 2) (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℚ)
    (U : Fin 4→Fin 2→ℚ) (k : ℕ) :
    (mixedLoop.stretchLabel 2 2 k).evaluate
      (ParameterizedPowerReduction.query_valid _ mixedLoop_valid k)
      (appendOne M A) U (fun _=>1)=
    mixedLoop.evaluate mixedLoop_valid (appendOne M (A^(k+1))) U (fun _=>1) :=
  ParameterizedPowerReduction.evaluate_query _ mixedLoop_valid _ M A U

example (M : Fin 2→Matrix (Fin 2) (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℚ)
    (U : Fin 4→Fin 2→ℚ) :
    (mixedLoop.stretchLabel 2 2 0).evaluate
      (ParameterizedPowerReduction.query_valid _ mixedLoop_valid 0)
      (appendOne M A) U (fun _=>1)=
    mixedLoop.evaluate mixedLoop_valid (appendOne M A) U (fun _=>1) := by
  simpa using ParameterizedPowerReduction.evaluate_query mixedLoop mixedLoop_valid 0 M A U

example {X K : Type} [Field K] [Algebra ℚ K] {dimension q b u : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop)
    (k : ℕ) (x : X) (hx : allowed x) (rawGraph : Bits) (g : MixedCode)
    (hd : encoding.decode rawGraph=some g) (hg : g.PlanarValid (b+1) u) :
    (ParameterizedPowerReduction.targetProblem basis ex M U F allowed).valid
      (BitEncoding.frame ((BitEncoding.unaryNat.prod ex).encode (k,x))++rawGraph) :=
  (ParameterizedPowerReduction.target_valid_iff basis ex M U F allowed _).mpr
    ⟨(k,x),rawGraph,rfl,hx,g,hd,hg⟩

example : (mixedLoop.stretchLabelDomains 2 2 4 2).unaries=
    [(0,3),(0,3),(1,1),(2,4),(3,4),(4,4),(5,4)] := by decide
example : (mixedLoop.stretchLabelDomains 2 2 4 0).unaries=mixedLoop.unaries := by decide

-- Endpoint permission at (0,0) alone does not license the ambient domain 1.
example : ¬PrescribedDomains.PathDomainTyping
    (fun _ : Fin 1=>fun x y : Fin 2=>x=0 ∧ y=0) 0 1 0 0 := by
  simp [PrescribedDomains.PathDomainTyping]
