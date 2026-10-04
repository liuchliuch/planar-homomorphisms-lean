import PlanarHom.BooleanSampleNormCertificates
import PlanarHom.BooleanSampledMetadataCertificates

noncomputable section
open Classical PlanarHom
open BooleanFieldTower BooleanFieldCollision

-- Equal-diagonal factors and a square radicand still require every sign.
private def c : Fin 1→ℚ:=fun _=>1
private def a : Fin 1→ℚ:=fun _=>0
private def w : Fin 1→ℚ:=fun _=>1/2
private theorem parameter_valid : BooleanExceptionalSource.SeparatedParameters
    (fun i=>(algebraMap ℚ ℝ) (c i)) (fun i=>(algebraMap ℚ ℝ) (a i))
    (fun i=>(algebraMap ℚ ℝ) (w i)) := by
  constructor
  · intro i; norm_num [c]
  · intro i; norm_num [c,a]
  · intro i; norm_num [w]
  · intro i; norm_num [w]
  · intro i hi; simp [a] at hi

example (n k:Fin 1→ℕ) : norm (radicands a w (1/2)) 1 (spectral c a w (1/2) n k)≠0 := by
  apply BooleanTowerRealEvaluation.norm_spectral_ne_zero (algebraMap ℚ ℝ) c a w _ n k parameter_valid
  norm_num

-- A zero divisor can be nonzero in the principal evaluation and zero in another sign.
example : BooleanFieldTowerEvaluation.eval (algebraMap ℚ ℝ) (fun _=>1) 1
    ((1,1):Tower ℚ 1) (fun _=>false)=2 := by
  norm_num [BooleanFieldTowerEvaluation.eval]
example : BooleanFieldTowerEvaluation.eval (algebraMap ℚ ℝ) (fun _=>1) 1
    ((1,1):Tower ℚ 1) (fun _=>true)=0 := by
  norm_num [BooleanFieldTowerEvaluation.eval]
example : norm (fun _=>(1:ℚ)) 1 ((1,1):Tower ℚ 1)=0 := by
  norm_num [BooleanFieldTower.norm,BooleanFieldTower.sub,BooleanFieldTower.add,
    BooleanFieldTower.neg,BooleanFieldTower.mul,BooleanFieldTower.embed]

-- Every actual accepted sample, including length zero, carries its full norm certificate.
example (q:ℚ) (hq:q∈BooleanEffectiveLengthSamples.samples c a w (fun _=>1) 1 0)
    (k:Fin 1→ℕ) :
    norm (radicands a w (algebraMap ℚ ℚ q)) 1
      (spectral c a w (algebraMap ℚ ℚ q) (fun _=>0) k)≠0 := by
  exact BooleanSampleNormCertificates.sampled_node_norm_ne_zero (algebraMap ℚ ℝ)
    c a w (fun _=>1) 1 0 q hq k parameter_valid
