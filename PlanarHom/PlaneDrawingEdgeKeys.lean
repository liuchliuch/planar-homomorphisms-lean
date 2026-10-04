import PlanarHom.SignedNandIdempotence
import PlanarHom.FisherTrianglePermutation

/-! Actual plane drawings for canonical simple edge lists extracted from a
drawn graph. Only repeated edge occurrences are removed; all vertices remain. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.MultiGraph.PlaneDrawing

variable {V E W F : Type} {G : MultiGraph V E} {H : MultiGraph W F}

def pullbackOriented (d : PlaneDrawing H) (v : V → W) (hv : Function.Injective v)
    (e : E → F) (he : Function.Injective e) (flip : E → Bool)
    (hs : ∀a,v (G.src a)=if flip a then H.dst (e a) else H.src (e a))
    (ht : ∀a,v (G.dst a)=if flip a then H.src (e a) else H.dst (e a)) : PlaneDrawing G where
  point := d.point ∘ v
  point_injective := d.point_injective.comp hv
  curve a := (d.curve (e a)).comp (orientedTime (flip a))
  curve_zero a := by cases hf : flip a <;> simp [Function.comp_apply,orientedTime,reverseTime,hf,hs,d.curve_zero,d.curve_one]
  curve_one a := by cases hf : flip a <;> simp [Function.comp_apply,orientedTime,reverseTime,hf,ht,d.curve_zero,d.curve_one]
  interior_injective a b s t hs' ht' h := by
    obtain ⟨hab,hst⟩ := d.interior_injective _ _ _ _ (orientedTime_inside (flip a) s hs')
      (orientedTime_inside (flip b) t ht') h
    have hab' := he hab
    subst b
    exact ⟨rfl,orientedTime_injective (flip a) hst⟩
  interior_avoids a t ht' z := d.interior_avoids _ _ (orientedTime_inside (flip a) t ht') (v z)

end PlanarHom.MultiGraph.PlaneDrawing

namespace PlanarHom.SignedNandNumeric
open MultiGraph

variable {W F : Type} (H : MultiGraph W F) {N : ℕ} (number : W ≃ Fin N)

def graphEdgeKey (e : F) : Edge := normalize ((number (H.src e)).val,(number (H.dst e)).val)

def listGraph (es : List Edge) (hb : ∀p∈es,p.1<N ∧ p.2<N) : MultiGraph (Fin N) (Fin es.length) where
  src i := ⟨(es.get i).1,(hb _ (List.get_mem _ _)).1⟩
  dst i := ⟨(es.get i).2,(hb _ (List.get_mem _ _)).2⟩

/-- A canonical numeric edge list is drawn by retaining its chosen original
curves, reversing their parameter direction when normalization requires it. -/
def drawingFromKeys (d : PlaneDrawing H) (es : List Edge) (hb : ∀p∈es,p.1<N ∧ p.2<N)
    (hnd : es.Nodup) (hcover : ∀p∈es,∃e,graphEdgeKey H number e=p) : PlaneDrawing (listGraph es hb) := by
  let select (i : Fin es.length) : F := Classical.choose (hcover _ (List.get_mem _ i))
  have key (i : Fin es.length) : graphEdgeKey H number (select i)=es.get i :=
    Classical.choose_spec (hcover _ (List.get_mem _ i))
  have inj : Function.Injective select := by
    intro i j hij
    apply hnd.get_inj_iff.mp
    rw [←key i,←key j,hij]
  let flip (i : Fin es.length) : Bool := decide ((es.get i).1≠(number (H.src (select i))).val)
  have ends (i : Fin es.length) :
      (es.get i=((number (H.src (select i))).val,(number (H.dst (select i))).val)) ∨
      (es.get i=((number (H.dst (select i))).val,(number (H.src (select i))).val)) := by
    have h := normalize_eq_or ((number (H.src (select i))).val,(number (H.dst (select i))).val)
    simpa only [←key i,graphEdgeKey] using h
  apply PlaneDrawing.pullbackOriented d number.symm number.symm.injective select inj flip
  · intro i
    apply number.injective
    rw [Equiv.apply_symm_apply]
    rcases ends i with h | h
    · have hf : flip i=false := by simp only [flip,h,Prod.fst]; simp
      rw [hf]
      apply Fin.ext
      exact congrArg Prod.fst h
    · by_cases he : (number (H.dst (select i))).val=(number (H.src (select i))).val
      · have hf : flip i=false := by simp only [flip,h,Prod.fst]; simp [he]
        rw [hf]
        apply Fin.ext
        exact (congrArg Prod.fst h).trans he
      · have hf : flip i=true := by simp only [flip,h,Prod.fst]; simp [he]
        rw [hf]
        apply Fin.ext
        exact congrArg Prod.fst h
  · intro i
    apply number.injective
    rw [Equiv.apply_symm_apply]
    rcases ends i with h | h
    · have hf : flip i=false := by simp only [flip,h,Prod.fst]; simp
      rw [hf]
      apply Fin.ext
      exact congrArg Prod.snd h
    · by_cases he : (number (H.dst (select i))).val=(number (H.src (select i))).val
      · have hf : flip i=false := by simp only [flip,h,Prod.fst]; simp [he]
        rw [hf]
        apply Fin.ext
        exact (congrArg Prod.snd h).trans he.symm
      · have hf : flip i=true := by simp only [flip,h,Prod.fst]; simp [he]
        rw [hf]
        apply Fin.ext
        exact congrArg Prod.snd h

end PlanarHom.SignedNandNumeric
