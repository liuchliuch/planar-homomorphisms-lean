import PlanarHom.FiniteWeightPowerRealAvailability

/-! The same target language simultaneously contains negative, zero and
fractional powers; original companions coexist and zero powers remain diagonal. -/
noncomputable section
open Classical PlanarHom PlanarHom.PositiveWeightRemoval
open PlanarHom.AlgebraicProductInterpolation PlanarHom.FiniteLanguageAliases
open PlanarHom.Complexity PlanarHom.Complexity.MixedCode

def regressionExponents : Fin 3→ℚ := ![-1,0,1/2]

variable {q bt ut dt : ℕ} (L : RealLanguage q bt ut)

example (old : Fin bt) (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hw : ∀i,0<L.weights i) (hnonzero : ∀i,L.matrices old i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction (L.finiteWeightPowerProblem hw regressionExponents) base :=
  L.lemma37_finiteRationalPowers old hs hw hnonzero hproj regressionExponents base available

example (D : Fin dt→Set (Fin q)) (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : D full=Set.univ) (hglobal : ∀x y,B old x y)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hw : ∀i,0<L.weights i) (hnonzero : ∀i,L.matrices old i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction
      (L.domainFiniteWeightPowerProblem D B T old hw regressionExponents) base :=
  L.lemma37_domainFiniteRationalPowers D B T old full hfull hglobal hs hw hnonzero hproj
    regressionExponents base available

example (i j : Fin q) (h : i≠j) :
    (finitePowerMatrices L.matricesK L.weightsK regressionExponents (Fin.natAdd bt 1) i j : ℝ)=0 := by
  rw [finitePowerMatrix_new_real]
  simp [diagonalPower,h]

example (i : Fin q) :
    (finitePowerMatrices L.matricesK L.weightsK regressionExponents (Fin.natAdd bt 1) i i : ℝ)=1 := by
  rw [finitePowerMatrix_new_real]
  simp [diagonalPower,regressionExponents]

example (i : Fin q) :
    (finitePowerMatrices L.matricesK L.weightsK regressionExponents (Fin.natAdd bt 0) i i : ℝ)=
      (L.weights i)⁻¹ := by
  rw [finitePowerMatrix_new_real]
  simp [diagonalPower,regressionExponents,Real.rpow_neg_one]

example (i : Fin q) :
    (finitePowerUnaryLanguage L.unariesK L.weightsK regressionExponents (Fin.natAdd ut 0) i : ℝ)=
      (L.weights i)⁻¹ := by
  rw [finitePowerUnary_new_real]
  simp [regressionExponents,Real.rpow_neg_one]

example (i : Fin q) :
    (finitePowerUnaryLanguage L.unariesK L.weightsK regressionExponents (Fin.natAdd ut 1) i : ℝ)=1 := by
  rw [finitePowerUnary_new_real]
  simp [regressionExponents]

example (l : Fin bt) (i j : Fin q) :
    (finitePowerMatrices L.matricesK L.weightsK regressionExponents (Fin.castAdd 3 l) i j : ℝ)=
      L.matrices l i j := by simp

example (l : Fin ut) (i : Fin q) :
    (finitePowerUnaryLanguage L.unariesK L.weightsK regressionExponents (Fin.castAdd 3 l) i : ℝ)=
      L.unaries l i := by simp

#check @RealLanguage.lemma37_finiteRationalPowers
#check @RealLanguage.lemma37_domainFiniteRationalPowers
#check @RealLanguage.finiteWeightPower_evaluate_coe
#check @RealLanguage.finiteWeightPower_evaluateRestricted_coe

-- The empty exponent family appends no binary or unary labels. The actual
-- finite-family machine still composes to the original supplied availability.
example (old : Fin bt) (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hw : ∀i,0<L.weights i) (hnonzero : ∀i,L.matrices old i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction
      (L.finiteWeightPowerProblem hw (fun i : Fin 0=>Fin.elim0 i)) base :=
  L.lemma37_finiteRationalPowers old hs hw hnonzero hproj (fun i : Fin 0=>Fin.elim0 i) base available

example (D : Fin dt→Set (Fin q)) (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : D full=Set.univ) (hglobal : ∀x y,B old x y)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hw : ∀i,0<L.weights i) (hnonzero : ∀i,L.matrices old i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction
      (L.domainFiniteWeightPowerProblem D B T old hw (fun i : Fin 0=>Fin.elim0 i)) base :=
  L.lemma37_domainFiniteRationalPowers D B T old full hfull hglobal hs hw hnonzero hproj
    (fun i : Fin 0=>Fin.elim0 i) base available

example (l : Fin bt) (i j : Fin q) :
    (finitePowerMatrices L.matricesK L.weightsK (fun i : Fin 0=>Fin.elim0 i) (Fin.castAdd 0 l) i j : ℝ)=
      L.matrices l i j :=
  finitePowerMatrix_old_real L.matricesK L.weightsK (fun i : Fin 0=>Fin.elim0 i) l i j
example (l : Fin ut) (i : Fin q) :
    (finitePowerUnaryLanguage L.unariesK L.weightsK (fun i : Fin 0=>Fin.elim0 i) (Fin.castAdd 0 l) i : ℝ)=
      L.unaries l i :=
  finitePowerUnary_old_real L.unariesK L.weightsK (fun i : Fin 0=>Fin.elim0 i) l i
