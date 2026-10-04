import PlanarHom.RootedColorRestriction
import PlanarHom.RootedRestrictionReduction
import PlanarHom.SourceSimulationOutputBounds

/-! Actual connected-input support-color restriction through the single-root
oracle, with the root chosen from the nonempty connected input. -/
noncomputable section
open Classical
namespace PlanarHom.RootedRestriction
local instance (priority := 10000) connectedColorRestrictionDecEq (α : Type*) : DecidableEq α := Classical.decEq α
open Complexity Complexity.MixedCode Turing MachineComposition PairProjectionMachines
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable [LinearOrder K] [IsStrictOrderedRing K] {dimension : ℕ}

def connectedValid (g : MixedCode) : Prop :=
  g.PlanarValid 1 0 ∧ (GraphComponentCode.support g).Connected ∧ 0<g.vertices

def connectedProblem (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C → K) : PromiseProblem :=
  restrictedEvaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w connectedValid

private theorem vertices_pos (g : MixedCode) (hg : connectedValid g) : 0 < g.vertices := by
  exact hg.2.2

private def prepareRoot (g : MixedCode) : ℕ × List (ℕ × MixedCode) := (0,[(0,g)])
private def recoverRoot (p : ℕ × List K) : K := p.2.headD 0

private def rootAnswer (M : Matrix C C K) (w : C → K) (X : Set C) (p : ℕ × MixedCode) : K :=
  if hg : p.2.Valid 1 0 then if hr : p.1 < p.2.vertices then
    (p.2.toMultiGraph hg).rootRestricted ⟨p.1,hr⟩ M w X else 0 else 0

private theorem fp_prepareRoot : FP MixedCode.encoding
    (BitEncoding.nat.prod RootedCodeMachines.inputEncoding.list) prepareRoot := by
  have h := (fp_const MixedCode.encoding BitEncoding.nat 0).pair (fp_id MixedCode.encoding)
  have hl := (h.pair (fp_const MixedCode.encoding RootedCodeMachines.inputEncoding.list [])).comp
    (ListMutationMachines.fp_cons RootedCodeMachines.inputEncoding)
  exact (fp_const MixedCode.encoding BitEncoding.nat 0).pair hl

private theorem fp_recoverRoot (basis : Module.Basis (Fin dimension) ℚ K) :
    FP (BitEncoding.nat.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recoverRoot :=
  (fp_snd _ _).comp (ListDecompositionMachines.fp_headD (numberFieldEncoding basis) 0)

private def connectedView (raw : Bits)
    (h : ∃g,MixedCode.encoding.decode raw=some g ∧ connectedValid g) :
    BitEncoding.ValidWord MixedCode.encoding := ⟨raw,by obtain ⟨g,hd,_⟩:=h; exact ⟨g,hd⟩⟩

private theorem connectedView_spec (raw : Bits)
    (h : ∃g,MixedCode.encoding.decode raw=some g ∧ connectedValid g) :
    connectedValid (connectedView raw h).value := by
  obtain ⟨g,hd,hg⟩:=h
  have hv : (connectedView raw ⟨g,hd,hg⟩).value=g := BitEncoding.ValidWord.value_eq hd
  simpa only [hv] using hg

/-- One literal root query reduces the connected color-submatrix problem to
single-root evaluation. No simultaneous pinning occurs. -/
def connectedSubmatrixToRoot (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (hs : ∀ i j,M i j=M j i) (w : C → K) (hw : ∀ i,0<w i)
    (X : Set C) (hX : ColorClosed M X) :
    PromisePolyTimeTuringReduction
      (connectedProblem basis (fun i j : X => M i.val j.val) (fun i : X => w i.val))
      (rootProblem basis M w X) := by
  let target := connectedProblem basis (fun i j : X => M i.val j.val) (fun i : X => w i.val)
  let source := rootProblem basis M w X
  let pre := composeComputers MixedCode.normalizer (Classical.choice fp_prepareRoot)
  let post := Classical.choice (fp_recoverRoot basis)
  let bound := rootReduction basis M w hw X
  apply nonadaptiveReduction (p:=bound.outputPolynomial) (BitEncoding.ValidWord.encoding MixedCode.encoding)
    BitEncoding.nat RootedCodeMachines.inputEncoding (numberFieldEncoding basis) (numberFieldEncoding basis)
    target source (fun a => prepareRoot a.value) (rootAnswer M w X) recoverRoot pre post
    connectedView (fun _ _=>rfl)
  · intro raw h query hq
    have hv:=connectedView_spec raw h
    have he : query=(0,(connectedView raw h).value) := by simpa [prepareRoot] using hq
    subst query
    exact ⟨_,RootedCodeMachines.inputEncoding.decode_encode _,hv.1,vertices_pos _ hv⟩
  · intro query hq
    obtain ⟨p,hd,hp,hr⟩:=hq
    rw [RootedCodeMachines.inputEncoding.decode_encode] at hd
    cases Option.some.inj hd
    change rootValue basis M w X (RootedCodeMachines.inputEncoding.encode query)=_
    rw [rootValue_decode basis M w X _ query (RootedCodeMachines.inputEncoding.decode_encode query) hp.1 hr]
    simp only [rootAnswer,dif_pos hp.1,dif_pos hr]
  · intro raw h
    have hv:=connectedView_spec raw h
    let g:=(connectedView raw h).value
    have hz:=vertices_pos g hv
    have hc:=rootRestricted_eq_submatrix g hv.1.1 hv.2.1 ⟨0,hz⟩ M hs w X hX
    have hgv : g.Valid 1 0 := hv.1.1
    have ha : rootAnswer M w X (0,g) =
        (g.toMultiGraph hgv).rootRestricted ⟨0,hz⟩ M w X := by
      dsimp only [rootAnswer]
      rw [dif_pos hgv,dif_pos hz]
    change (numberFieldEncoding basis).encode (rootAnswer M w X (0,g)) = evaluationValue basis _ _ _ raw
    rw [ha,hc]
    rw [evaluationValue_decode basis _ _ _ raw g (BitEncoding.ValidWord.decode_raw (connectedView raw h)) hv.1.1,
      evaluate_homogeneous]
  · exact bound.output_length_bound

/-- The connected restriction now uses the original homogeneous weighted source
oracle through the constructed rooted program. -/
def connectedSubmatrixReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (hs : ∀ i j,M i j=M j i) (w : C → K) (hw : ∀ i,0<w i)
    (X : Set C) (hX : ColorClosed M X) :
    PromisePolyTimeTuringReduction
      (connectedProblem basis (fun i j : X => M i.val j.val) (fun i : X => w i.val))
      (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w) :=
  (connectedSubmatrixToRoot basis M hs w hw X hX).trans (rootReduction basis M w hw X)

end PlanarHom.RootedRestriction
