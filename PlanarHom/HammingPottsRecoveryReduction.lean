import PlanarHom.HammingPottsRootRecovery
import PlanarHom.FullLogarithmicPottsReduction
import PlanarHom.GraphNonadaptiveReduction

/-! NEW actual Potts-to-selected-tensor reduction. The input is the ordinary
raw planar graph problem; the query graph is unchanged, and exact field-root
recovery is compiled with full oracle answer-length accounting. -/
noncomputable section
namespace PlanarHom.HammingPottsRecoveryReduction
open Complexity Complexity.MixedCode PairProjectionMachines MachineComposition
open HammingPottsProductIdentities HammingPottsFieldFamily HammingPottsTensorPartition
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {dimension d q : ℕ}

def prepare (g : MixedCode) : ℕ×List MixedCode := (g.vertices,[g])

theorem fp_prepare : FP encoding (BitEncoding.unaryNat.prod encoding.list) prepare := by
  have hs:=((fp_id encoding).pair (fp_const encoding encoding.list [])).comp
    (ListMutationMachines.fp_cons encoding)
  exact fp_vertices.pair hs

def rawView (basis : Module.Basis (Fin dimension) ℚ K) (s : ℕ) (raw : Bits)
    (h : (FullLogarithmicPottsReduction.pottsProblem basis s).valid raw) :
    BitEncoding.ValidWord encoding := ⟨raw,by obtain ⟨g,hd,_⟩:=h;exact ⟨g,hd⟩⟩

theorem rawView_spec (basis : Module.Basis (Fin dimension) ℚ K) (s : ℕ) (raw : Bits)
    (h : (FullLogarithmicPottsReduction.pottsProblem basis s).valid raw) :
    (rawView basis s raw h).value.PlanarValid 1 0 := by
  obtain ⟨g,hd,hg⟩:=h
  have he:=BitEncoding.ValidWord.value_eq (w:=rawView basis s raw ⟨g,hd,hg⟩) hd
  rw [he]
  exact hg

def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (sizes : Fin d→ℕ) (hsizes : ∀r,0<sizes r) (s : ℕ) (hoccurs : ∃r,sizes r=s)
    (e : Fin q≃Color sizes) :
    PromisePolyTimeTuringReduction (FullLogarithmicPottsReduction.pottsProblem basis s)
      (evaluationProblem basis (fun _ : Fin 1=>targetK sizes s e)
        (fun u : Fin 0=>u.elim0) (fun _=>1)) := by
  let H:=fun _ : Fin 1=>targetK (K:=K) sizes s e
  let A:=fun _ : Fin 1=>(FullLogarithmicProductIdentities.pottsMatrix : Matrix (Fin s) (Fin s) K)
  let UH : Fin 0→Fin q→K:=fun u=>u.elim0
  let UA : Fin 0→Fin s→K:=fun u=>u.elim0
  let source:=evaluationProblem basis H UH (fun _=>1)
  let target:=FullLogarithmicPottsReduction.pottsProblem basis s
  let pre:=composeComputers normalizer (Classical.choice fp_prepare)
  let post:=Classical.choice (HammingPottsRootRecovery.fp_recover basis sizes s)
  let hb:=PartitionOutputBounds.exists_polynomial_raw_mixed_evaluation_length_bound
    basis H UH (fun _=>1)
  let p:=Classical.choose hb
  have hbound:=Classical.choose_spec hb
  apply nonadaptiveReduction (p:=p) (BitEncoding.ValidWord.encoding encoding)
    BitEncoding.unaryNat encoding (numberFieldEncoding basis) (numberFieldEncoding basis)
    target source (prepare ∘ BitEncoding.ValidWord.value) (totalEvaluation H UH (fun _=>1))
    (HammingPottsRootRecovery.recover basis sizes s) pre post (rawView basis s) (fun _ _=>rfl)
  · intro raw h query hquery
    have he : query=(rawView basis s raw h).value:=List.mem_singleton.mp hquery
    subst query
    exact ⟨_,encoding.decode_encode _,rawView_spec basis s raw h⟩
  · intro query hquery
    obtain ⟨g,hd,hg⟩:=hquery
    rw [encoding.decode_encode] at hd
    cases Option.some.inj hd
    change evaluationValue basis H UH (fun _=>1) (encoding.encode query)=_
    rw [evaluationValue_encode _ _ _ _ _ hg.1,totalEvaluation_valid _ _ _ _ hg.1]
  · intro raw h
    let z:=rawView basis s raw h
    have hg:=rawView_spec basis s raw h
    have hc : HammingPottsRootRecovery.recover basis sizes s
        (z.value.vertices,[totalEvaluation H UH (fun _=>1) z.value]) =
        totalEvaluation A UA (fun _=>1) z.value := by
      rw [totalEvaluation_valid _ _ _ _ hg.1,totalEvaluation_valid _ _ _ _ hg.1]
      change HammingPottsRootRecovery.recover basis sizes s
        (z.value.vertices,[z.value.evaluate hg.1 H UH (fun _=>1)]) =
        z.value.evaluate hg.1 A UA (fun _=>1)
      rw [evaluate_homogeneous,evaluate_homogeneous]
      simpa only [Fintype.card_fin] using
        HammingPottsRootRecovery.recover_partition basis (z.value.toMultiGraph hg.1)
          sizes hsizes s hoccurs e
    change (numberFieldEncoding basis).encode
      (HammingPottsRootRecovery.recover basis sizes s
        (z.value.vertices,[totalEvaluation H UH (fun _=>1) z.value]))=target.value raw
    rw [hc,totalEvaluation_valid _ _ _ _ hg.1]
    exact (evaluationValue_decode basis A UA (fun _=>1) raw z.value
      (BitEncoding.ValidWord.decode_raw z) hg.1).symm
  · intro raw h
    obtain ⟨g,hd,hg⟩:=h
    change (evaluationValue basis H UH (fun _=>1) raw).length≤p.eval raw.length
    rw [evaluationValue_decode _ _ _ _ raw g hd hg.1]
    exact hbound raw g hg.1 hd

end PlanarHom.HammingPottsRecoveryReduction
