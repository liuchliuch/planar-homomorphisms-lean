import PlanarHom.FixedRealNonnegativeVertexWeights

#print axioms PlanarHom.FixedRealSurvivingWeights.theoremA13
#print axioms PlanarHom.FixedRealSurvivingWeights.omitted_weight_zero
#print axioms PlanarHom.FixedRealSurvivingWeights.surviving_class_zero_weights
#print PlanarHom.FixedRealSurvivingWeights.theoremA13

open PlanarHom
example {K : Type} [Field K] (φ : K →+* ℝ)
    (M : Matrix (Fin 3) (Fin 3) K) (hs : ∀ i j,M i j=M j i) :
    FixedRealSurvivingWeights.SurvivingClass φ M (fun _ => 0) hs :=
  FixedRealSurvivingWeights.surviving_class_zero_weights φ M (fun _ => 0) hs (fun _ => rfl)

example {K : Type} [Field K] (φ : K →+* ℝ)
    (M : Matrix (Fin 0) (Fin 0) K) (w : Fin 0 → K) (hs : ∀ i j,M i j=M j i) :
    FixedRealSurvivingWeights.SurvivingClass φ M w hs :=
  FixedRealSurvivingWeights.surviving_class_zero_weights φ M w hs (fun i => i.elim0)
