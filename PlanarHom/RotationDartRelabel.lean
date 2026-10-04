import PlanarHom.RotationFaceCycleDuality
import PlanarHom.FinitePermutationCycleTransport

/-! NEW transport of literal rotations through vertex/occurrence-direction
relabelings. Reversal and endpoint incidence are proved fields; Euler and all
face cycles are transported by an actual permutation conjugacy. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
open Kasteleyn PlanarityLRRealization
variable {V E W F : Type*}

/-- A literal occurrence relabeling with an independently chosen direction
flip on each original edge. -/
def twistedDartEquiv (e : E≃F) (flip : E→Bool) : Dart E≃Dart F where
  toFun a := (e a.1,a.2 ^^ flip a.1)
  invFun a := (e.symm a.1,a.2 ^^ flip (e.symm a.1))
  left_inv a := by
    rcases a with ⟨a,b⟩
    simp only [e.symm_apply_apply]
    cases b <;> cases flip a <;> rfl
  right_inv a := by
    rcases a with ⟨a,b⟩
    simp only [e.apply_symm_apply]
    cases b <;> cases flip (e.symm a) <;> rfl

theorem twistedDartEquiv_reverse (e : E≃F) (flip : E→Bool) (a : Dart E) :
    twistedDartEquiv e flip (reversePerm E a)=reversePerm F (twistedDartEquiv e flip a) := by
  rcases a with ⟨a,b⟩
  cases b <;> cases h : flip a <;> simp [twistedDartEquiv,reversePerm,h]

structure DartRelabel (G : MultiGraph V E) (H : MultiGraph W F) where
  vertex : V≃W
  dart : Dart E≃Dart F
  reverse : ∀a,dart (reversePerm E a)=reversePerm F (dart a)
  host : ∀a,(H.dartPair (dart a)).1=vertex (G.dartPair a).1

namespace DartRelabel
variable {G : MultiGraph V E} {H : MultiGraph W F} (e : DartRelabel G H)
variable [DecidableEq (Dart E)] [DecidableEq (Dart F)]

 def rows (R : RotationRows G) : RotationRows H where
  row w := (R.row (e.vertex.symm w)).map e.dart
  nodup w := (R.nodup _).map e.dart.injective
  mem w a := by
    rw [List.mem_map]
    constructor
    · rintro ⟨b,hb,rfl⟩
      rw [e.host,(R.mem _ _).mp hb,e.vertex.apply_symm_apply]
    · intro ha
      refine ⟨e.dart.symm a,(R.mem _ _).mpr ?_,e.dart.apply_symm_apply a⟩
      apply e.vertex.injective
      rw [←e.host,e.dart.apply_symm_apply,e.vertex.apply_symm_apply,ha]

 theorem rows_rotation (R : RotationRows G) (a : Dart E) :
    (e.rows R).rotation (e.dart a)=e.dart (R.rotation a) := by
  rw [RotationRows.rotation_apply,e.host]
  change ((R.row (e.vertex.symm (e.vertex (G.dartPair a).1))).map e.dart).formPerm (e.dart a)=_
  rw [e.vertex.symm_apply_apply]
  exact map_formPerm_apply e.dart e.dart.injective _ (R.nodup _) ((R.mem _ _).mpr rfl)

 theorem rows_face [Fintype V] [Fintype E] [Fintype W] [Fintype F]
    (R : RotationRows G) (a : Dart E) :
    (e.rows R).facePerm (e.dart a)=e.dart (R.facePerm a) := by
  change (e.rows R).rotation (reversePerm F (e.dart a))=e.dart (R.rotation (reversePerm E a))
  rw [←e.reverse,e.rows_rotation]

 theorem face_count [Fintype V] [Fintype E] [Fintype W] [Fintype F] (R : RotationRows G) :
    FinitePermutationCycles.count (e.rows R).facePerm=FinitePermutationCycles.count R.facePerm := by
  symm
  exact FinitePermutationCycles.count_semiconj _ _ e.dart (fun a=>(e.rows_face R a).symm)

 include e in
 theorem edge_card [Fintype E] [Fintype F] : Fintype.card E=Fintype.card F := by
  have h := Fintype.card_congr e.dart
  simp only [Dart,Fintype.card_prod,Fintype.card_bool] at h
  omega

 theorem euler [Fintype V] [Fintype E] [Fintype W] [Fintype F] (R : RotationRows G)
    (h : Fintype.card V+FinitePermutationCycles.count R.facePerm=Fintype.card E+2) :
    Fintype.card W+FinitePermutationCycles.count (e.rows R).facePerm=Fintype.card F+2 := by
  rw [e.face_count,←e.edge_card,←Fintype.card_congr e.vertex]
  exact h

end DartRelabel
end PlanarHom.MultiGraph
