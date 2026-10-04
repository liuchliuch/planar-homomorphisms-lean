import PlanarHom.ColoringFramedCanvasRows
import PlanarHom.FaceSpliceRowReflection

/-! The base face program has exactly the original local cyclic successors on
each literal patch block, including the initial rail cycle. -/
noncomputable section
open Classical
namespace PlanarHom.HostRowSystem
 theorem ofRotationRows_rotation_any {V E : Type} {d₁ d₂ : DecidableEq (MultiGraph.Kasteleyn.Dart E)}
    (G : MultiGraph V E) (R : @PlanarityLRRealization.RotationRows V E G d₁) :
    @HostRowSystem.rotation V (MultiGraph.Kasteleyn.Dart E) d₂ (@ofRotationRows V E d₁ G R)=
      @PlanarityLRRealization.RotationRows.rotation V E G d₁ R := by
  have hd : d₁=d₂ := Subsingleton.elim _ _
  subst d₂
  rfl
end PlanarHom.HostRowSystem
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 def baseRotation (f : NumericFormula) : Equiv.Perm (Dart f) := baseFace f*reversePerm (Edge f)

 theorem seedRows_rotation_step (N : ℕ) (e : Fin N) (b : Bool) :
    (seedRows N).rotation (e,b)=if b then ((finRotate N).symm e,false) else (finRotate N e,true) := by
  cases b <;> simp [RotationRows.rotation_apply,seedRows,seedRow,seedGraph,MultiGraph.dartPair,List.formPerm_pair]

 theorem baseRotation_seed (f : NumericFormula) (a : MultiGraph.Kasteleyn.Dart (Fin (3*f.1))) :
    baseRotation f (seedDart f a)=seedDart f ((seedRows (3*f.1)).rotation a) := by
  rcases a with ⟨e,b⟩
  rw [seedRows_rotation_step]
  cases b <;> rfl

 theorem baseRotation_patch (f : NumericFormula) (i : Canvas.Index f)
    (a : MultiGraph.Kasteleyn.Dart (PatchEdge f i)) :
    baseRotation f (patchDart f i a)=
      patchDart f i ((FramedMacro.cutRows (canvasCell f i).shape).rotation a) := by
  rw [FramedMacro.cutRows_rotation]
  rcases a with ⟨e,b⟩
  cases b <;> rfl

 theorem baseRotation_local (f : NumericFormula) (c : PatchIndex f) (a : LocalDart f c) :
    baseRotation f (dartEquiv f ⟨c,a⟩)=dartEquiv f ⟨c,(localSystem f c).rotation a⟩ := by
  cases c with
  | none =>
      change baseRotation f (seedDart f a)=seedDart f ((localSystem f none).rotation a)
      rw [localSystem,HostRowSystem.ofRotationRows_rotation_any]
      exact baseRotation_seed f a
  | some i =>
      change baseRotation f (patchDart f i a)=patchDart f i ((localSystem f (some i)).rotation a)
      rw [localSystem,HostRowSystem.ofRotationRows_rotation_any]
      exact baseRotation_patch f i a

 def localLift (f : NumericFormula) (c : PatchIndex f) : LocalDart f c→Dart f :=
  fun a=>dartEquiv f ⟨c,a⟩

 theorem localLift_injective (f : NumericFormula) (c : PatchIndex f) : Function.Injective (localLift f c) := by
  intro a b h
  have he := (dartEquiv f).injective h
  exact eq_of_heq (Sigma.mk.inj he).2

 def blockWord (f : NumericFormula) (c : PatchIndex f) (v : LocalVertex f c) : List (Dart f) :=
  ((localSystem f c).row v).map (localLift f c)

 theorem blockWord_baseRotation (f : NumericFormula) (c : PatchIndex f) (v : LocalVertex f c)
    (a : Dart f) (ha : a∈blockWord f c v) :
    baseRotation f a=(blockWord f c v).formPerm a := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  have hm := PlanarityLRRealization.map_formPerm_apply (localLift f c) (localLift_injective f c)
    ((localSystem f c).row v) ((localSystem f c).nodup v) hb
  change baseRotation f (dartEquiv f ⟨c,b⟩)=_
  rw [baseRotation_local]
  change localLift f c (((localSystem f c).row ((localSystem f c).host b)).formPerm b)=_
  rw [((localSystem f c).mem v b).mp hb]
  exact hm.symm
end PlanarHom.ColoringEmitter.FramedCanvas
