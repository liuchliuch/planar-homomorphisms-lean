import PlanarHom.BiasedUnaryProductMaps
import PlanarHom.EndpointUnaryDecoration
import PlanarHom.SignedNandFieldHardness

/-! Actual reduction from signed NAND to every positive symmetric biased
nonsingular Boolean matrix. Loops realize the diagonal unary; product
interpolation supplies the fixed-prime activity and the signed center unary. -/
noncomputable section
open Classical
namespace PlanarHom.BiasedPositiveHardness
open Complexity Complexity.MixedCode FiniteLanguageAliases ProductCompatibility BiasedBinaryProductSeparation
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

abbrev matrixFin (B : Matrix Bool Bool K) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => B (finTwoEquiv i) (finTwoEquiv j)

def noUnary (C : Type) : Fin 0 → C → K := fun u => u.elim0

def primeUnary (p : ℕ) : Fin 2 → K := fun i => if finTwoEquiv i then (p:K) else 1

theorem diagonal_eq (B : Matrix Bool Bool K) (i : Fin 2) :
    matrixFin B i i=bitWeight (B false false) (B true true) (finTwoEquiv i) := by
  cases h : finTwoEquiv i <;> simp [matrixFin,bitWeight,h]

theorem decorated_pair (B : Matrix Bool Bool K) (hs : ∀i j,B i j=B j i) (p : ℕ) :
    (fun e : Fin 2 × Fin 2 => EndpointUnaryDecoration.decorated (matrixFin B) (primeUnary p) e.1 e.2)=
      (fun e => pairWeight (B false false) (B false true*(p:K)) (B true true*(p:K)^2)
        (finTwoEquiv e.1,finTwoEquiv e.2)) := by
  funext e
  have hs' := hs true false
  cases h0 : finTwoEquiv e.1 <;> cases h1 : finTwoEquiv e.2 <;>
    simp [EndpointUnaryDecoration.decorated,matrixFin,primeUnary,pairWeight,h0,h1,hs'] <;> ring

theorem nand_pair : (fun e : Fin 2 × Fin 2 => nandFin (K:=K) e.1 e.2)=
    (fun e => pairWeight (1:K) 1 0 (finTwoEquiv e.1,finTwoEquiv e.2)) := by
  funext e
  cases h0 : finTwoEquiv e.1 <;> cases h1 : finTwoEquiv e.2 <;>
    simp [nandFin,nandMatrix,SignedNandExactOneClause.nandWeight,pairWeight,h0,h1]

/-- Every query is an ordinary raw planar mixed code. The original language
stays available throughout both unary interpolations and matrix normalization. -/
def reduction_with_prime (basis : Module.Basis (Fin dimension) ℚ K) (ι : K →+* ℝ)
    (B : Matrix Bool Bool K) (hs : ∀i j,B i j=B j i) (hpos : ∀i j,0<ι (B i j))
    (hbias : B false false≠B true true) (p : ℕ) (hp : p.Prime)
    (hmap : HasProductMaps (pairWeight (B false false) (B false true*(p:K)) (B true true*(p:K)^2))
      (pairWeight (1:K) 1 0)) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => nandFin) (fun _ : Fin 1 => negativeFin) (fun _ => 1))
      (evaluationProblem basis (fun _ : Fin 1 => matrixFin B) (noUnary (Fin 2)) (fun _ => 1)) := by
  let M : Fin 1 → Matrix (Fin 2) (Fin 2) K := fun _ => matrixFin B
  let U0 : Fin 0 → Fin 2 → K := noUnary (Fin 2)
  let H : Fin 1 → Fin 2 → K := appendOne U0 (fun i => matrixFin B i i)
  let D : Fin 2 → K := primeUnary p
  let U1 : Fin 2 → Fin 2 → K := appendOne H D
  let U2 : Fin 3 → Fin 2 → K := appendOne U1 negativeFin
  have hnonzero (i : Fin 2) : matrixFin B i i≠0 := by
    intro hz
    have h := hpos (finTwoEquiv i) (finTwoEquiv i)
    change 0<ι (matrixFin B i i) at h
    rw [hz,map_zero] at h
    exact (lt_irrefl 0 h)
  have hh (i : Fin 2) : H 0 i=matrixFin B i i := by
    exact congrFun (appendOne_aux U0 (fun i => matrixFin B i i)) i
  have hhfun : H 0=(fun i : Fin 2 => bitWeight (B false false) (B true true) (finTwoEquiv i)) :=
    funext (fun i => (hh i).trans (diagonal_eq B i))
  have hhd : HasProductMaps (H 0) D := by
    rw [hhfun]
    exact unary_product_maps_fin ι (B false false) (B true true) (hpos false false) (hpos true true)
      hbias (bitWeight 1 (p:K))
  have hhn : HasProductMaps (U1 (Fin.castAdd 1 (0:Fin 1))) negativeFin := by
    change HasProductMaps (appendOne H D (Fin.castAdd 1 (0:Fin 1))) negativeFin
    rw [appendOne_old,hhfun]
    exact unary_product_maps_fin ι (B false false) (B true true) (hpos false false) (hpos true true)
      hbias (negativeUnary (K:=K))
  let rH := diagonalUnaryAppendReduction basis M U0 (fun _ => 1) (0:Fin 1)
  let rD := unaryAppendProductReduction basis M H (fun _ => 1) D (0:Fin 1)
    (fun i hz => False.elim (hnonzero i ((hh i).symm.trans hz))) hhd
  let rN := unaryAppendProductReduction basis M U1 (fun _ => 1) negativeFin (Fin.castAdd 1 (0:Fin 1))
    (fun i hz => False.elim (hnonzero i (by simpa only [U1,appendOne_old,hh] using hz))) hhn
  let P := EndpointUnaryDecoration.decorated (matrixFin B) D
  let MP := appendOne M P
  let MN := appendOne M nandFin
  have hD (i : Fin 2) : U2 (Fin.castAdd 1 (Fin.last 1)) i=D i := by
    simp only [U2,U1,appendOne_old,appendOne_aux]
  let rP := EndpointUnaryDecoration.reduction basis M U2 (fun _ => 1) (0:Fin 1) (Fin.castAdd 1 (Fin.last 1))
  have rP' : PromisePolyTimeTuringReduction (evaluationProblem basis MP U2 (fun _ => 1))
      (evaluationProblem basis M U2 (fun _ => 1)) := by
    simpa only [hD] using rP
  have hpK : (p:K)≠0 := by
    intro hz
    have hh : (p:ℝ)=0 := by simpa using congrArg ι hz
    exact hp.ne_zero (by exact_mod_cast hh)
  have hd (i : Fin 2) : D i≠0 := by
    change (if finTwoEquiv i then (p:K) else 1)≠0
    split
    · exact hpK
    · exact one_ne_zero
  have hP (i j : Fin 2) : P i j≠0 := by
    apply mul_ne_zero
    · apply mul_ne_zero (hd i)
      intro hz
      have h := hpos (finTwoEquiv i) (finTwoEquiv j)
      change 0<ι (matrixFin B i j) at h
      rw [hz,map_zero] at h
      exact lt_irrefl _ h
    · exact hd j
  have hmaps : HasProductMaps (fun e : Fin 2 × Fin 2 => P e.1 e.2) (fun e => nandFin e.1 e.2) := by
    rw [nand_pair]
    change HasProductMaps (fun e : Fin 2 × Fin 2 => EndpointUnaryDecoration.decorated (matrixFin B) (primeUnary p) e.1 e.2) _
    rw [decorated_pair B hs p]
    exact binary_product_maps_fin _ _ _ _ _ _ hmap
  let rB := binaryProductReduction basis MP MN U2 (fun _ => 1) (Fin.last 1)
    (fun l hl => appendOne_eq_of_ne_aux M nandFin P l hl)
    (by simpa only [MP,appendOne_aux] using (fun i j hz => False.elim (hP i j hz)))
    (by simpa only [MP,MN,appendOne_aux] using hmaps)
  have rUseB : PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => nandFin) U2 (fun _ => 1))
      (evaluationProblem basis MN U2 (fun _ => 1)) := by
    simpa only [MN,Function.comp_def,appendOne_aux] using
      binaryRelabelReduction basis (fun _ : Fin 1 => Fin.last 1) MN U2 (fun _ => 1)
  have rUseU : PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => nandFin) (fun _ : Fin 1 => negativeFin) (fun _ => 1))
      (evaluationProblem basis (fun _ : Fin 1 => nandFin) U2 (fun _ => 1)) := by
    simpa only [U2,Function.comp_def,appendOne_aux] using
      unaryRelabelReduction basis (fun _ : Fin 1 => Fin.last 2) (fun _ : Fin 1 => nandFin) U2 (fun _ => 1)
  exact rUseU.trans (rUseB.trans (rB.trans (rP'.trans (rN.trans (rD.trans rH)))))

/-- The fixed prime exists in the actual coefficient field. Therefore no
activity-availability or product-map premise remains in the hardness theorem. -/
theorem promisedSharpPHard [Module.Finite ℚ K] (basis : Module.Basis (Fin dimension) ℚ K)
    (ι : K →+* ℝ) (B : Matrix Bool Bool K) (hs : ∀i j,B i j=B j i)
    (hpos : ∀i j,0<ι (B i j)) (hbias : B false false≠B true true)
    (hdet : B false false*B true true≠B false true^2) :
    PromisedSharpPHard (evaluationProblem basis (fun _ : Fin 1 => B) (noUnary Bool) (fun _ => 1)) := by
  obtain ⟨p,hp,hmap⟩ := exists_prime_product_maps ι (B false false) (B false true) (B true true)
    (hpos false false) (hpos false true) (hpos true true) hdet
  have h := (signed_fin_hard basis).trans (reduction_with_prime basis ι B hs hpos hbias p hp (hmap 1 1 0))
  have he := evaluationProblem_colorReindex basis finTwoEquiv (fun _ : Fin 1 => B) (noUnary Bool) (fun _ => 1)
  have hnone : (fun (l : Fin 0) i => noUnary Bool l (finTwoEquiv i))=noUnary (K:=K) (Fin 2) := by
    funext l; exact l.elim0
  rw [hnone] at he
  exact he ▸ h

end PlanarHom.BiasedPositiveHardness
