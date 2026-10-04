import PlanarHom.PlanarityLRComponentFaceRoot

/-! NEW actual runtime orientation products on every non-omitted component face.
This is the finite Kasteleyn theorem's exact per-cycle input. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRConstraints
open PlanarityFaceCode FinitePermutationCycles

 def componentOrientation (g : MixedCode) (r : ℕ) (orientation : ℕ → Bool) : ComponentEdge g r → Bool :=
  fun e => orientation e.val.val

 theorem component_cycleWord_boundarySign (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (r : ℕ) (base a : Dart (ComponentEdge g r)) (orientation : ℕ → Bool)
    (hodd : ∀ f∈boundedFaces g bits, FaceOdd orientation (boundaryById g bits f))
    (hne : ¬(componentFace g hg r (directRotationRows g hg bits)).SameCycle a
      (componentFaceRoot g hg bits r base)) :
    boundarySign (componentOrientation g r orientation)
        (cycleWord (componentFace g hg r (directRotationRows g hg bits)) a)=
      (-1:ℤ)^((cycleWord (componentFace g hg r (directRotationRows g hg bits)) a).length+1) := by
  have hmem := component_nonroot_faceId_bounded g hg bits r base a hne
  have hh := (hodd _ hmem).boundarySign
  have hp := boundaryById_perm_componentFaceWord g hg bits r a
  rw [boundarySign_perm orientation hp,hp.length_eq,List.length_map] at hh
  simpa only [boundarySign,List.map_map,Function.comp_def,dartSign,componentOrientation,
    eraseDart,componentDartLift] using hh

 theorem component_face_products_of_faceOdd (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (r : ℕ) (base : Dart (ComponentEdge g r)) (orientation : ℕ → Bool)
    (hodd : ∀ f∈boundedFaces g bits, FaceOdd orientation (boundaryById g bits f)) :
    ∀ q : CycleClass (componentFace g hg r (directRotationRows g hg bits)),
      q≠classOf (componentFace g hg r (directRotationRows g hg bits)) (componentFaceRoot g hg bits r base) →
      (∏a : {a // classOf (componentFace g hg r (directRotationRows g hg bits)) a=q},
        dartSign (componentOrientation g r orientation) a.val)=
        (-1:ℤ)^(Fintype.card {a // classOf (componentFace g hg r (directRotationRows g hg bits)) a=q}+1) := by
  intro q
  induction q using Quotient.inductionOn with
  | h a =>
      intro hne
      change (∏b : {b // classOf (componentFace g hg r (directRotationRows g hg bits)) b=
        classOf (componentFace g hg r (directRotationRows g hg bits)) a},
        dartSign (componentOrientation g r orientation) b.val)=
        (-1:ℤ)^(Fintype.card {b // classOf (componentFace g hg r (directRotationRows g hg bits)) b=
          classOf (componentFace g hg r (directRotationRows g hg bits)) a}+1)
      rw [cycleFiber_product (componentFace g hg r (directRotationRows g hg bits)) a
        (dartSign (componentOrientation g r orientation)),
        cycleFiber_card (componentFace g hg r (directRotationRows g hg bits)) a]
      exact component_cycleWord_boundarySign g hg bits r base a orientation hodd
        (fun h => hne (Quotient.sound h))

/-- Exact component face-product equations for the actual polynomial-time
orientationLog output. No planarity assumption is needed for this runtime fact. -/
theorem orientationLog_component_face_products (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : ℕ) (base : Dart (ComponentEdge g r)) :
    ∀ q : CycleClass (componentFace g hg r (directRotationRows g hg (decideAligned g).2)),
      q≠classOf (componentFace g hg r (directRotationRows g hg (decideAligned g).2))
        (componentFaceRoot g hg (decideAligned g).2 r base) →
      (∏a : {a // classOf (componentFace g hg r (directRotationRows g hg (decideAligned g).2)) a=q},
        dartSign (componentOrientation g r (logOrientation (orientationLog g))) a.val)=
        (-1:ℤ)^(Fintype.card {a // classOf (componentFace g hg r (directRotationRows g hg (decideAligned g).2)) a=q}+1) :=
  component_face_products_of_faceOdd g hg (decideAligned g).2 r base (logOrientation (orientationLog g))
    (orientationLog_faceOdd g hg)

 theorem exists_orientationLog_component_face_products (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : ℕ) [Nonempty (ComponentEdge g r)] :
    ∃ omitted : CycleClass (componentFace g hg r (directRotationRows g hg (decideAligned g).2)),
      ∀ q, q≠omitted →
      (∏a : {a // classOf (componentFace g hg r (directRotationRows g hg (decideAligned g).2)) a=q},
        dartSign (componentOrientation g r (logOrientation (orientationLog g))) a.val)=
        (-1:ℤ)^(Fintype.card {a // classOf (componentFace g hg r (directRotationRows g hg (decideAligned g).2)) a=q}+1) := by
  let base : Dart (ComponentEdge g r) := (Classical.choice inferInstance,true)
  exact ⟨classOf _ (componentFaceRoot g hg (decideAligned g).2 r base),
    orientationLog_component_face_products g hg r base⟩

end PlanarHom.PlanarityLRRealization
