import PlanarHom.SurfaceComponentMachines
import PlanarHom.SurfaceComponentRowSemantics
import PlanarHom.SurfaceRowEvaluation
import PlanarHom.GraphComponentTractability

/-! NEW actual component closure for supplied rotation rows. Each output
carries its computed row table and a proved no-larger homology dimension. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceRowEvaluation
open Complexity Complexity.MixedCode GraphComponentCode
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension b u : ℕ}

def ConnectedValid (b u ambient : ℕ) (p : Input) : Prop :=
  Valid b u ambient p ∧ (support p.1).Connected ∧ 0<p.1.vertices

def ConnectedEvaluable (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K) : Prop :=
  FP (encoding.restrict (ConnectedValid b u ambient)) (numberFieldEncoding basis)
    (fun p:{p:Input // ConnectedValid b u ambient p} => p.val.1.evaluate (graph_valid p.property.1) M U w)

theorem components_promises {ambient : ℕ} {p : Input} (hp : Valid b u ambient p) :
    ∀q∈SurfaceComponentCode.components p.1 p.2,ConnectedValid b u ambient q := by
  intro q hq
  obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hq
  obtain ⟨hg,R,hr,hd⟩ := hp
  refine ⟨⟨extract_valid p.1 hg xs,SurfaceComponentCode.typedRows p.1 hg R xs hxs,
    SurfaceComponentCode.extractRows_realizes p.1 hg p.2 R hr xs hxs,
    (SurfaceComponentCode.typedRows_homology_finrank_le p.1 hg R xs hxs).trans hd⟩,
    extract_connected p.1 hg xs hxs,?_⟩
  exact List.length_pos_iff.mpr (parts_nonempty p.1 xs hxs)

def promisedComponents (ambient : ℕ) (p : {p:Input // Valid b u ambient p}) :
    List {p:Input // ConnectedValid b u ambient p} :=
  (SurfaceComponentCode.components p.val.1 p.val.2).attachWith (ConnectedValid b u ambient)
    (components_promises p.property)

theorem fp_promisedComponents (ambient : ℕ) :
    FP (encoding.restrict (Valid b u ambient)) (encoding.restrict (ConnectedValid b u ambient)).list
      (promisedComponents (b:=b) (u:=u) ambient) := by
  have h := (fp_code_view (encoding.restrict (Valid b u ambient)) encoding Subtype.val (fun _=>rfl)).comp
    SurfaceComponentCode.fp_components
  apply h.transportOutput
  intro p
  simp [promisedComponents,BitEncoding.list,BitEncoding.restrict]

theorem evaluable_of_connected (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K)
    (h : ConnectedEvaluable ambient basis M U w) : Evaluable ambient basis M U w := by
  have he := (fp_promisedComponents (b:=b) (u:=u) ambient).comp
    (ListMapMachines.fp_map _ _ _ h)
  have hp := he.comp (MaterializedFieldListMachines.fp_product basis)
  apply hp.congr
  intro p
  rw [evaluate_components p.val.1 (graph_valid p.property) M U w]
  apply congrArg List.prod
  simp only [Function.comp_apply,promisedComponents,List.map_attachWith]
  have hlist : ((GraphComponentCode.components p.val.1).map (totalEvaluation M U w))=
      (SurfaceComponentCode.components p.val.1 p.val.2).map (fun c=>totalEvaluation M U w c.1) := by
    simp [GraphComponentCode.components,SurfaceComponentCode.components,SurfaceComponentCode.extract,List.map_map]
  rw [hlist,←List.attach_map_val (l:=SurfaceComponentCode.components p.val.1 p.val.2)
    (f:=fun c=>totalEvaluation M U w c.1)]
  apply List.map_congr_left
  intro c _
  exact (totalEvaluation_valid M U w c.val.1 (graph_valid (components_promises p.property c.val c.property).1)).symm

theorem connected_of_evaluable (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K)
    (h : Evaluable ambient basis M U w) : ConnectedEvaluable ambient basis M U w := by
  let view : {p:Input // ConnectedValid b u ambient p}→{p:Input // Valid b u ambient p} :=
    fun p=>⟨p.val,p.property.1⟩
  exact (h.transportInput (ea:=encoding.restrict (ConnectedValid b u ambient)) view (fun _=>rfl)).congr
    (fun _=>rfl)

end PlanarHom.SurfaceRowEvaluation
