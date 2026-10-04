import PlanarHom.RadialPottsShortConnected
import PlanarHom.OccurrenceMatchings

/-! NEW reconstruction: both literal colors of short edges have bijective
endpoint maps, so each separately covers every white vertex exactly once. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPottsTile
open MultiGraph

def baseEndpoint {k : ℕ} (p : HalfShort k × Bool) : White k :=
  if p.2 then oddWhite p.1 else evenWhite p.1

theorem baseEndpoint_surjective (k : ℕ) : Function.Surjective (@baseEndpoint k) := by
  rintro ⟨r,i⟩
  let e : HalfShort k := ⟨r,⟨i.val/2,by have := i.isLt; omega⟩⟩
  rcases Nat.mod_two_eq_zero_or_one i.val with h | h
  · refine ⟨(e,false),?_⟩
    apply white_ext
    · rfl
    · change 2*(i.val/2)=i.val
      omega
  · refine ⟨(e,true),?_⟩
    apply white_ext
    · rfl
    · change 2*(i.val/2)+1=i.val
      omega

theorem baseEndpoint_bijective (k : ℕ) : Function.Bijective (@baseEndpoint k) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨baseEndpoint_surjective k,?_⟩
  rw [Fintype.card_prod,Fintype.card_bool,card_halfShort,card_white]
  ring

def shiftWhite {k : ℕ} (w : White k) : White k :=
  ⟨w.1,⟨(w.2.val+1)%(8*w.1.val+4),Nat.mod_lt _ (by omega)⟩⟩

theorem shiftWhite_injective (k : ℕ) : Function.Injective (@shiftWhite k) := by
  rintro ⟨r,i⟩ ⟨s,j⟩ h
  have hrs := congrArg Sigma.fst h
  change r=s at hrs
  subst s
  have hv := congrArg (fun w : White k => w.2.val) h
  change (i.val+1)%(8*r.val+4)=(j.val+1)%(8*r.val+4) at hv
  have hi := i.isLt
  have hj := j.isLt
  apply white_ext
  · rfl
  · change i.val=j.val
    have hm (a : Fin (8*r.val+4)) : (a.val+1)%(8*r.val+4)=
        if a.val+1<8*r.val+4 then a.val+1 else 0 := by
      split_ifs with ha
      · exact Nat.mod_eq_of_lt ha
      · have he : a.val+1=8*r.val+4 := by have := a.isLt; omega
        rw [he,Nat.mod_self]
    rw [hm i,hm j] at hv
    split_ifs at hv <;> omega

theorem shiftWhite_bijective (k : ℕ) : Function.Bijective (@shiftWhite k) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨shiftWhite_injective k,rfl⟩

def shortEndpoint {k : ℕ} (color : Bool) (p : HalfShort k × Bool) : White k :=
  if color then (if p.2 then nextWhite p.1 else oddWhite p.1)
  else switch (baseEndpoint p)

theorem blueEndpoint_eq_shift {k : ℕ} (p : HalfShort k × Bool) :
    shortEndpoint true p=shiftWhite (baseEndpoint p) := by
  rcases p with ⟨⟨r,i⟩,b⟩
  cases b
  · apply white_ext
    · rfl
    · change 2*i.val+1=(2*i.val+1)%(8*r.val+4)
      exact (Nat.mod_eq_of_lt (by have := i.isLt; omega)).symm
  · apply white_ext
    · rfl
    · rfl

/-- Every short color is an actual perfect matching of endpoint occurrences. -/
theorem shortEndpoint_bijective (k : ℕ) (color : Bool) :
    Function.Bijective (@shortEndpoint k color) := by
  cases color
  · exact switch_involutive.bijective.comp (baseEndpoint_bijective k)
  · have he : (@shortEndpoint k true)=shiftWhite ∘ baseEndpoint := by
      funext p
      exact blueEndpoint_eq_shift p
    rw [he]
    exact (shiftWhite_bijective k).comp (baseEndpoint_bijective k)

noncomputable def shortEndpointEquiv (k : ℕ) (color : Bool) :
    (HalfShort k × Bool) ≃ White k := Equiv.ofBijective _ (shortEndpoint_bijective k color)

@[simp] theorem shortEndpoint_src {k : ℕ} (e : HalfShort k × Bool) :
    shortEndpoint e.2 (e.1,false)=(shortGraph k).src e := by rcases e with ⟨e,b⟩; cases b <;> rfl

@[simp] theorem shortEndpoint_dst {k : ℕ} (e : HalfShort k × Bool) :
    shortEndpoint e.2 (e.1,true)=(shortGraph k).dst e := by rcases e with ⟨e,b⟩; cases b <;> rfl

def shortIndex {k : ℕ} (color : Bool) (w : White k) : HalfShort k :=
  ((shortEndpointEquiv k color).symm w).1

theorem shortIndex_endpoint {k : ℕ} (color : Bool) (e : HalfShort k) (b : Bool) :
    shortIndex color (shortEndpoint color (e,b))=e := by
  change ((shortEndpointEquiv k color).symm ((shortEndpointEquiv k color) (e,b))).1=e
  simp
end PlanarHom.RadialPottsTile
