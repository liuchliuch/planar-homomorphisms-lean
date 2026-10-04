import PlanarHom.IntegerStraightDrawing
import Mathlib.Tactic
import PlanarHom.RadialPottsTile

/-! NEW exact integer coordinates. White rings have clipped square corners;
all four terminal bundles lie on the outer square in the required order. -/
namespace PlanarHom.RadialPottsTileCoordinates
open IntegerStraightDrawing RadialPottsTile

def turn (s : Fin 4) (p : Point) : Point :=
  ![p,(p.2,-p.1),(-p.1,-p.2),(-p.2,p.1)] s

/-- An open side of an integer square determines its side, radius, and offset. -/
theorem turn_injective_sectors (s t : Fin 4) (r q x y : ℤ)
    (hr : 0<r) (hq : 0<q) (hx : -r<x ∧ x<r) (hy : -q<y ∧ y<q)
    (he : turn s (x,r)=turn t (y,q)) : s=t ∧ r=q ∧ x=y := by
  fin_cases s <;> fin_cases t <;> norm_num [turn,Prod.mk.injEq] at he ⊢ <;> omega

def whiteSide {k : ℕ} (w : White k) : Fin 4 :=
  ⟨w.2.val/(2*w.1.val+1),by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0<2*w.1.val+1)).mpr
    have := w.2.isLt
    omega⟩

def whiteOffset {k : ℕ} (w : White k) : ℤ :=
  (w.2.val%(2*w.1.val+1) : ℕ) - (w.1.val : ℤ)

def point {k : ℕ} : Vertex k → Point
  | .inl w => turn (whiteSide w) (whiteOffset w,(w.1.val:ℤ)+1)
  | .inr p => turn p.1 (2*(p.2.val:ℤ)-(k:ℤ)+1,(k:ℤ)+1)

theorem whiteOffset_bounds {k : ℕ} (w : White k) :
    -(w.1.val:ℤ)-1<whiteOffset w ∧ whiteOffset w<(w.1.val:ℤ)+1 := by
  have h:=Nat.mod_lt w.2.val (by omega : 0<2*w.1.val+1)
  unfold whiteOffset
  omega

theorem portOffset_bounds {k : ℕ} (a : Fin k) :
    -(k:ℤ)-1<2*(a.val:ℤ)-(k:ℤ)+1 ∧ 2*(a.val:ℤ)-(k:ℤ)+1<(k:ℤ)+1 := by
  have := a.isLt
  omega

theorem point_injective {k : ℕ} : Function.Injective (@point k) := by
  intro u v he
  cases u with
  | inl u =>
    cases v with
    | inl v =>
      have hh := turn_injective_sectors (whiteSide u) (whiteSide v)
        ((u.1.val:ℤ)+1) ((v.1.val:ℤ)+1) (whiteOffset u) (whiteOffset v)
        (by omega) (by omega) (by have hb := whiteOffset_bounds u; omega)
        (by have hb := whiteOffset_bounds v; omega) he
      apply congrArg Sum.inl
      rcases u with ⟨r,i⟩
      rcases v with ⟨s,j⟩
      have hrs : r=s := Fin.ext (by dsimp at hh; omega)
      subst s
      have hd := congrArg Fin.val hh.1
      have hm := hh.2.2
      dsimp [whiteSide,whiteOffset] at hd hm
      have hi := Nat.mod_add_div i.val (2*r.val+1)
      have hj := Nat.mod_add_div j.val (2*r.val+1)
      have hmcast : ((i.val % (2*r.val+1):ℕ):ℤ)=((j.val % (2*r.val+1):ℕ):ℤ)  := (sub_left_inj).mp hm
      have hm' : i.val % (2*r.val+1)=j.val % (2*r.val+1) := by exact_mod_cast hmcast
      have hij : i.val=j.val := by rw [←hd,←hm'] at hj; omega
      have heq : i=j := Fin.ext hij
      subst j
      rfl
    | inr v =>
      have hh := turn_injective_sectors (whiteSide u) v.1
        ((u.1.val:ℤ)+1) ((k:ℤ)+1) (whiteOffset u) (2*(v.2.val:ℤ)-(k:ℤ)+1)
        (by omega) (by omega) (by have hb := whiteOffset_bounds u; omega)
        (by have hb := portOffset_bounds v.2; omega) he
      have := u.1.isLt
      omega
  | inr u =>
    cases v with
    | inl v =>
      have hh := turn_injective_sectors u.1 (whiteSide v)
        ((k:ℤ)+1) ((v.1.val:ℤ)+1) (2*(u.2.val:ℤ)-(k:ℤ)+1) (whiteOffset v)
        (by omega) (by omega) (by have hb := portOffset_bounds u.2; omega)
        (by have hb := whiteOffset_bounds v; omega) he
      have := v.1.isLt
      omega
    | inr v =>
      have hh := turn_injective_sectors u.1 v.1 ((k:ℤ)+1) ((k:ℤ)+1)
        (2*(u.2.val:ℤ)-(k:ℤ)+1) (2*(v.2.val:ℤ)-(k:ℤ)+1)
        (by omega) (by omega) (by have hb := portOffset_bounds u.2; omega)
        (by have hb := portOffset_bounds v.2; omega) he
      apply congrArg Sum.inr
      apply Prod.ext hh.1
      apply Fin.ext
      omega

end PlanarHom.RadialPottsTileCoordinates
