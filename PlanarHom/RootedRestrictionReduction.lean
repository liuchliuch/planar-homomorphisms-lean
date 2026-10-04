import PlanarHom.RootedHomogeneousSemantics
import PlanarHom.RootedConditionalSemantics
import PlanarHom.RootedQueryMachines
import PlanarHom.GraphNonadaptiveReduction

/-! Actual polynomial-time single-root restriction. The source oracle is the
original homogeneous weighted planar problem; no pinning language is added. -/
noncomputable section
open Classical
namespace PlanarHom.RootedRestriction
local instance (priority := 10000) rootedRestrictionReductionDecEq0 (α : Type*) : DecidableEq α := Classical.decEq α
open Complexity Complexity.MixedCode Turing MachineComposition
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable [LinearOrder K] [IsStrictOrderedRing K] {dimension : ℕ}

/-- Input is a binary root index and the complete original raw mixed graph.
Only the one homogeneous edge label is permitted and there are no unary labels. -/
def rootValid (raw : Bits) : Prop :=
  ∃ p : ℕ × MixedCode, RootedCodeMachines.inputEncoding.decode raw=some p ∧
    p.2.PlanarValid 1 0 ∧ p.1 < p.2.vertices

def rootValue (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C → K) (X : Set C) (raw : Bits) : Bits :=
  match RootedCodeMachines.inputEncoding.decode raw with
  | none => []
  | some p => if hg : p.2.Valid 1 0 then if hr : p.1 < p.2.vertices then
      (numberFieldEncoding basis).encode
        ((p.2.toMultiGraph hg).rootRestricted ⟨p.1,hr⟩ M w X) else [] else []

def rootProblem (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C → K) (X : Set C) : PromiseProblem :=
  ⟨rootValid,rootValue basis M w X⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem rootValue_decode (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C → K) (X : Set C) (raw : Bits) (p : ℕ × MixedCode)
    (hd : RootedCodeMachines.inputEncoding.decode raw=some p)
    (hg : p.2.Valid 1 0) (hr : p.1 < p.2.vertices) :
    rootValue basis M w X raw = (numberFieldEncoding basis).encode
      ((p.2.toMultiGraph hg).rootRestricted ⟨p.1,hr⟩ M w X) := by
  simp only [rootValue,hd,dif_pos hg,dif_pos hr]

private def rawView (raw : Bits) (h : rootValid raw) :
    BitEncoding.ValidWord RootedCodeMachines.inputEncoding :=
  ⟨raw,by obtain ⟨p,hd,_⟩ := h; exact ⟨p,hd⟩⟩

private theorem rawView_spec (raw : Bits) (h : rootValid raw) :
    (rawView raw h).value.2.PlanarValid 1 0 ∧
      (rawView raw h).value.1 < (rawView raw h).value.2.vertices := by
  obtain ⟨p,hd,hp⟩ := h
  have hv : (rawView raw ⟨p,hd,hp⟩).value = p := BitEncoding.ValidWord.value_eq hd
  simpa only [hv] using hp

/-- The mathematical fixed query graphs and coefficients are compiled into
literal programs. Every query is planar and every oracle extension is handled
with polynomial total work, query, and answer communication cost. -/
def rootReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C → K) (hw : ∀ i,0 < w i) (X : Set C) :
    PromisePolyTimeTuringReduction (rootProblem basis M w X)
      (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w) := by
  let data := exists_computed_root_queries M w hw X
  let k := Classical.choose data
  let graphs := Classical.choose (Classical.choose_spec data)
  let c := Classical.choose (Classical.choose_spec (Classical.choose_spec data))
  have correct := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec data))
  let norm := BitEncoding.prodNormalizer BitEncoding.natNormalizer MixedCode.normalizer
  let pre := composeComputers norm (Classical.choice (fp_prepare graphs))
  let post := Classical.choice (fp_recover basis c)
  let source := evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w
  let bound := evaluationProblem_output_bound basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w
  let p := Classical.choose bound
  have hp := Classical.choose_spec bound
  apply nonadaptiveReduction (p:=p) (BitEncoding.ValidWord.encoding RootedCodeMachines.inputEncoding)
    BitEncoding.nat MixedCode.encoding (numberFieldEncoding basis) (numberFieldEncoding basis)
    (rootProblem basis M w X) source (fun a => prepare graphs a.value)
    (totalEvaluation (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w)
    (recover c) pre post rawView (fun _ _ => rfl)
  · intro raw h query hquery
    have hv := rawView_spec raw h
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hquery
    exact ⟨_,MixedCode.encoding.decode_encode _,RootedCodeMachines.attach_planarValid
      (graphs j).2.2.val (graphs j).2.2.property 0 _ hv.1 ⟨_,hv.2⟩ (by decide)⟩
  · intro query hquery
    have hv : query.PlanarValid 1 0 := (planarInput_encode_iff 1 0 query).mp hquery
    change evaluationValue basis _ _ _ (MixedCode.encoding.encode query) = _
    rw [evaluationValue_encode _ _ _ _ query hv.1,totalEvaluation_valid _ _ _ query hv.1]
  · intro raw h
    have hv := rawView_spec raw h
    let a := (rawView raw h).value
    have hc := correct a.2 hv.1 ⟨a.1,hv.2⟩
    rw [MultiGraph.atRoot_restricted] at hc
    have hr : recover c ((prepare graphs a).1,
        (prepare graphs a).2.map (totalEvaluation (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w)) =
        (a.2.toMultiGraph hv.1.1).rootRestricted ⟨a.1,hv.2⟩ M w X := by
      simp only [prepare,List.map_ofFn,recover_ofFn]
      exact hc.symm
    change (numberFieldEncoding basis).encode (recover c _) = rootValue basis M w X raw
    rw [hr]
    exact (rootValue_decode basis M w X raw a (BitEncoding.ValidWord.decode_raw (rawView raw h))
      hv.1.1 hv.2).symm
  · exact hp

end PlanarHom.RootedRestriction
