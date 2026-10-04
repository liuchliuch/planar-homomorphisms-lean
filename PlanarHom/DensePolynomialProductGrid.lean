import PlanarHom.DenseGridSampling
import PlanarHom.DenseOriginalDegreeBounds

/-! NEW polynomial-length dense product program for an arbitrary materialized
list. The runtime evaluates on a fixed-dimensional grid and interpolates, so
unreduced symbolic fractions cannot accumulate exponentially. -/
noncomputable section
namespace PlanarHom.DensePolynomial
open Complexity PairProjectionMachines

 def inputSquare {A:Type} (e:BitEncoding A) (a:A) : ℕ := (e.encode a).length^2

 theorem fp_inputSquare {A:Type} (e:BitEncoding A) : FP e BitEncoding.unaryNat (inputSquare e) := by
  have h:FP e BitEncoding.unaryNat (fun a=>(e.encode a).length):=⟨InputLengthMachine.computer e⟩
  exact ((h.pair h).comp UnaryArithmeticMachines.fp_mul).congr (fun a=>(pow_two _).symm)

 def productSample (n:ℕ) (ps:List (Code n)) (point:List ℚ) : ℚ :=
    (ps.map (fun p=>evaluate n p point)).prod

 def productGrid (n:ℕ) (ps:List (Code n)) : Code n :=
    gridRecover n (inputSquare (encoding n).list ps) (productSample n ps)

 theorem productSample_eq (n:ℕ) (ps:List (Code n)) (point:List ℚ) :
    productSample n ps point=evalHom n point ((ps.map (interpret n)).prod) := by
  rw [productSample,map_list_prod]
  simp only [List.map_map,Function.comp_def,evaluate_semantics]

 theorem productGrid_eq (n:ℕ) (ps:List (Code n)) :
    interpret n (productGrid n ps)=(ps.map (interpret n)).prod :=
  gridRecover_eq n _ _ _ (product_input_degree n ps) (fun point _=>productSample_eq n ps point)

 theorem fp_productSample (n:ℕ) : FP ((encoding n).list.prod rationalCode.list) rationalCode
    (fun p=>productSample n p.1 p.2) := by
  let e:=encoding n
  have hb:=((fp_snd rationalCode.list e).pair (fp_fst rationalCode.list e)).comp (fp_evaluate n)
  have hm:=((fp_snd e.list rationalCode.list).pair (fp_fst e.list rationalCode.list)).comp
    (ListContextMachines.fp_mapWithContext rationalCode.list e rationalCode _ hb)
  exact hm.comp (MaterializedFieldListMachines.fp_product rationalBasis)

 theorem fp_productGrid (n:ℕ) : FP (encoding n).list (encoding n) (productGrid n) :=
    ((fp_inputSquare (encoding n).list).pair (fp_id (encoding n).list)).comp
      (fp_gridRecover (encoding n).list (productSample n) (fp_productSample n) n)

end PlanarHom.DensePolynomial
