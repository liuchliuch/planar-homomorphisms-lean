import PlanarHom.PlanarityRowComponentFaceRoot
import PlanarHom.PlanarityLRComponentFaceProducts

/-! NEW literal component face-product equations for the arbitrary-row
polynomial orientation program, with its actual omitted representative. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.PlanarityRowFaceCode
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRealization
open FinitePermutationCycles
local instance {A : Type*} (P : Equiv.Perm A) : DecidableEq (CycleClass P) := Classical.decEq _
 theorem component_cycleWord_boundarySign (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (r : ℕ) (base a : Dart (ComponentEdge g r)) (orientation : ℕ → Bool)
    (hodd : ∀ f∈boundedFaces g rows, FaceOdd orientation (boundaryById g rows f))
    (hne : ¬(componentFace g hg r (R)).SameCycle a
      (componentFaceRoot g hg rows R hrows r base)) :
    boundarySign (componentOrientation g r orientation)
        (cycleWord (componentFace g hg r (R)) a)=
      (-1:ℤ)^((cycleWord (componentFace g hg r (R)) a).length+1) := by
  have hmem := component_nonroot_faceId_bounded g hg rows R hrows r base a hne
  have hh := (hodd _ hmem).boundarySign
  have hp := boundaryById_perm_componentFaceWord g hg rows R hrows r a
  rw [boundarySign_perm orientation hp,hp.length_eq,List.length_map] at hh
  simpa only [boundarySign,List.map_map,Function.comp_def,dartSign,componentOrientation,
    eraseDart,componentDartLift] using hh

 theorem component_face_products_of_faceOdd (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (r : ℕ) (base : Dart (ComponentEdge g r)) (orientation : ℕ → Bool)
    (hodd : ∀ f∈boundedFaces g rows, FaceOdd orientation (boundaryById g rows f)) :
    ∀ q : CycleClass (componentFace g hg r (R)),
      q≠classOf (componentFace g hg r (R)) (componentFaceRoot g hg rows R hrows r base) →
      (∏a : {a // classOf (componentFace g hg r (R)) a=q},
        dartSign (componentOrientation g r orientation) a.val)=
        (-1:ℤ)^(Fintype.card {a // classOf (componentFace g hg r (R)) a=q}+1) := by
  intro q
  induction q using Quotient.inductionOn with
  | h a =>
      intro hne
      change (∏b : {b // classOf (componentFace g hg r (R)) b=
        classOf (componentFace g hg r (R)) a},
        dartSign (componentOrientation g r orientation) b.val)=
        (-1:ℤ)^(Fintype.card {b // classOf (componentFace g hg r (R)) b=
          classOf (componentFace g hg r (R)) a}+1)
      have hp : (∏b : {b // classOf (componentFace g hg r R) b=classOf (componentFace g hg r R) a},
          dartSign (componentOrientation g r orientation) b.val)=
          boundarySign (componentOrientation g r orientation) (cycleWord (componentFace g hg r R) a) := by
        convert cycleFiber_product (componentFace g hg r R) a (dartSign (componentOrientation g r orientation)) using 1 <;>
          congr <;> exact Subsingleton.elim _ _
      have hc : Fintype.card {b // classOf (componentFace g hg r R) b=classOf (componentFace g hg r R) a}=
          (cycleWord (componentFace g hg r R) a).length := by
        simpa only [Fintype.card_fin] using (Fintype.card_congr (cycleFiberEquiv (componentFace g hg r R) a)).symm
      rw [hp,hc]
      exact component_cycleWord_boundarySign g hg rows R hrows r base a orientation hodd
        (fun h => hne (Quotient.sound h))


 theorem orientationLog_component_face_products (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R)
    (r : ℕ) (base : Dart (ComponentEdge g r)) :
    ∀q : CycleClass (componentFace g hg r R),
      q≠classOf (componentFace g hg r R) (componentFaceRoot g hg rows R hrows r base) →
      (∏a : {a // classOf (componentFace g hg r R) a=q},
        dartSign (componentOrientation g r (logOrientation (orientationLog g rows))) a.val)=
        (-1:ℤ)^(Fintype.card {a // classOf (componentFace g hg r R) a=q}+1) :=
  component_face_products_of_faceOdd g hg rows R hrows r base (logOrientation (orientationLog g rows))
    (orientationLog_faceOdd g hg rows R hrows)
end PlanarHom.PlanarityRowFaceCode
