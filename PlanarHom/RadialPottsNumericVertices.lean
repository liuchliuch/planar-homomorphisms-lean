import PlanarHom.RadialPottsAssembly
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

/-! Explicit polynomial-size numeric indices for every radial vertex. Ring
prefixes are 4r², so no opaque finite-type enumeration is used by the serializer. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile

 def whiteIndex {k : ℕ} (w : White k) : ℕ := 4*w.1.val^2+w.2.val

 theorem whiteIndex_lt {k : ℕ} (w : White k) : whiteIndex w<4*k^2 := by
  have hr := w.1.isLt
  have hi := w.2.isLt
  dsimp [whiteIndex]
  nlinarith

 theorem whiteIndex_injective {k : ℕ} : Function.Injective (@whiteIndex k) := by
  intro u v h
  have hu := u.2.isLt
  have hv := v.2.isLt
  dsimp [whiteIndex] at h
  have hr : u.1.val=v.1.val := by
    rcases lt_trichotomy u.1.val v.1.val with hl | he | hl
    · nlinarith
    · exact he
    · nlinarith
  apply white_ext u v hr
  nlinarith

 def whiteIndexEquiv (k : ℕ) : White k ≃ Fin (4*k^2) :=
  Equiv.ofBijective (fun w => ⟨whiteIndex w,whiteIndex_lt w⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun _ _ h => whiteIndex_injective (congrArg Fin.val h),by rw [RadialPottsTile.card_white,Fintype.card_fin]⟩)

 def dartIndex {m : ℕ} (d : Medial.Dart (Fin m)) : ℕ := 2*d.1.val+if d.2 then 1 else 0

 def dartIndexEquiv (m : ℕ) : Medial.Dart (Fin m) ≃ Fin (2*m) :=
  ((Equiv.prodCongr (Equiv.refl (Fin m)) finTwoEquiv.symm).trans finProdFinEquiv).trans
    (finCongr (Nat.mul_comm m 2))

 @[simp] theorem dartIndexEquiv_val {m : ℕ} (d : Medial.Dart (Fin m)) :
    (dartIndexEquiv m d).val=dartIndex d := by
  rcases d with ⟨e,b⟩
  cases b <;> simp [dartIndexEquiv,dartIndex,finProdFinEquiv,finTwoEquiv] <;> omega

 def vertexCount (m k : ℕ) : ℕ := m*(4*k^2)+(2*m)*k

 def vertexIndexEquiv (m k : ℕ) : Vertex (Fin m) k ≃ Fin (vertexCount m k) :=
  (Equiv.sumCongr
    ((Equiv.prodCongr (Equiv.refl (Fin m)) (whiteIndexEquiv k)).trans finProdFinEquiv)
    ((Equiv.prodCongr (dartIndexEquiv m) (Equiv.refl (Fin k))).trans finProdFinEquiv)).trans finSumFinEquiv

 @[simp] theorem vertexIndexEquiv_white {m k : ℕ} (e : Fin m) (w : White k) :
    (vertexIndexEquiv m k (.inl (e,w))).val=(4*k^2)*e.val+whiteIndex w := by
  change whiteIndex w+(4*k^2)*e.val=(4*k^2)*e.val+whiteIndex w
  omega

 @[simp] theorem vertexIndexEquiv_port {m k : ℕ} (d : Medial.Dart (Fin m)) (a : Fin k) :
    (vertexIndexEquiv m k (.inr (d,a))).val=m*(4*k^2)+k*dartIndex d+a.val := by
  change m*(4*k^2)+(a.val+k*(dartIndexEquiv m d).val)=_
  rw [dartIndexEquiv_val]
  omega
end PlanarHom.RadialPotts.Assembly
