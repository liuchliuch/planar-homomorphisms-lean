import PlanarHom.RootedPlanarity
import Mathlib.Data.Fintype.Option

/-! Finite simultaneous attachment of actual rooted planar gadgets. -/
noncomputable section
open Classical

namespace PlanarHom.MultiGraph
universe u v w x y
variable {V : Type v} {E : Type w} {I : Type u}
variable {W : I → Type x} {F : I → Type y}

def attachFamilyVertex (r : I → V) (i : I) : PUnit ⊕ W i → V ⊕ Sigma W :=
  Sum.elim (fun _ => Sum.inl (r i)) (fun z => Sum.inr ⟨i,z⟩)

def attachFamily (G : MultiGraph V E) (r : I → V) (H : ∀ i, RootedGraph (W i) (F i)) :
    MultiGraph (V ⊕ Sigma W) (E ⊕ Sigma F) where
  src := Sum.elim (fun e => Sum.inl (G.src e))
    (fun e => attachFamilyVertex r e.1 ((H e.1).src e.2))
  dst := Sum.elim (fun e => Sum.inl (G.dst e))
    (fun e => attachFamilyVertex r e.1 ((H e.1).dst e.2))

def attachFamilyReindex {J : Type u} (G : MultiGraph V E) (e : I ≃ J)
    {W' : J → Type x} {F' : J → Type y} (r : J → V)
    (H : ∀ j, RootedGraph (W' j) (F' j)) :
    IncidenceEquiv (G.attachFamily (fun i => r (e i)) (fun i => H (e i)))
      (G.attachFamily r H) where
  vertex := Equiv.sumCongr (Equiv.refl V) (Equiv.sigmaCongr e (fun _ => Equiv.refl _))
  edge := Equiv.sumCongr (Equiv.refl E) (Equiv.sigmaCongr e (fun _ => Equiv.refl _))
  src_eq := by
    rintro (f | ⟨i,f⟩)
    · rfl
    · cases h : (H (e i)).src f <;> simp [attachFamily, attachFamilyVertex, Equiv.sigmaCongr, h]
  dst_eq := by
    rintro (f | ⟨i,f⟩)
    · rfl
    · cases h : (H (e i)).dst f <;> simp [attachFamily, attachFamilyVertex, Equiv.sigmaCongr, h]

def optionFamilyEquiv (X : Type*) (Y : Option I → Type*) :
    (X ⊕ (Σ i : I, Y (some i))) ⊕ Y none ≃ X ⊕ Sigma Y where
  toFun := Sum.elim (Sum.elim Sum.inl (fun q => Sum.inr ⟨some q.1,q.2⟩))
    (fun z => Sum.inr ⟨none,z⟩)
  invFun := Sum.elim (fun z => Sum.inl (Sum.inl z))
    (fun q => match q with
      | ⟨none,z⟩ => Sum.inr z
      | ⟨some i,z⟩ => Sum.inl (Sum.inr ⟨i,z⟩))
  left_inv := by rintro ((z | ⟨i,z⟩) | z) <;> rfl
  right_inv := by rintro (z | ⟨i,z⟩); rfl; cases i <;> rfl

def attachFamilyOptionEquiv (G : MultiGraph V E)
    {W' : Option I → Type x} {F' : Option I → Type y} (r : Option I → V)
    (H : ∀ i, RootedGraph (W' i) (F' i)) :
    IncidenceEquiv
      ((G.attachFamily (fun i => r (some i)) (fun i => H (some i))).attachRooted
        (H none) (Sum.inl (r none)))
      (G.attachFamily r H) where
  vertex := optionFamilyEquiv V W'
  edge := optionFamilyEquiv E F'
  src_eq := by
    rintro ((e | ⟨i,e⟩) | e)
    · rfl
    · cases h : (H (some i)).src e <;>
        simp [attachFamily, attachFamilyVertex, attachRooted, attachRootedVertex,
          optionFamilyEquiv, h]
    · cases h : (H none).src e <;>
        simp [attachFamily, attachFamilyVertex, attachRooted, attachRootedVertex,
          optionFamilyEquiv, h]
  dst_eq := by
    rintro ((e | ⟨i,e⟩) | e)
    · rfl
    · cases h : (H (some i)).dst e <;>
        simp [attachFamily, attachFamilyVertex, attachRooted, attachRootedVertex,
          optionFamilyEquiv, h]
    · cases h : (H none).dst e <;>
        simp [attachFamily, attachFamilyVertex, attachRooted, attachRootedVertex,
          optionFamilyEquiv, h]

def sumEmptyEquiv (X Y : Type*) [IsEmpty Y] : X ⊕ Y ≃ X where
  toFun := Sum.elim id isEmptyElim
  invFun := Sum.inl
  left_inv := by rintro (x | y); rfl; exact isEmptyElim y
  right_inv _ := rfl

def attachFamilyEmptyEquiv (G : MultiGraph V E) [IsEmpty I] (r : I → V)
    (H : ∀ i, RootedGraph (W i) (F i)) : IncidenceEquiv G (G.attachFamily r H) where
  vertex := (sumEmptyEquiv V (Sigma W)).symm
  edge := (sumEmptyEquiv E (Sigma F)).symm
  src_eq _ := rfl
  dst_eq _ := rfl

/-- The finite-family result is proved by actual single-root attachments and
occurrence-preserving incidence equivalences. -/
theorem Planar.attachFamily [Fintype I] [Finite V] [Finite E]
    [∀ i, Fintype (W i)] [∀ i, Fintype (F i)]
    {G : MultiGraph V E} (hG : G.Planar) (r : I → V)
    (H : ∀ i, RootedGraph (W i) (F i)) (hH : ∀ i, (H i).Planar) :
    (G.attachFamily r H).Planar := by
  have hgeneral : ∀ (J : Type u) [Fintype J],
      ∀ (W' : J → Type x) (F' : J → Type y) [∀ j, Fintype (W' j)] [∀ j, Fintype (F' j)]
        (r' : J → V) (H' : ∀ j, RootedGraph (W' j) (F' j)),
        (∀ j, (H' j).Planar) → (G.attachFamily r' H').Planar := by
    intro J _
    apply Fintype.induction_empty_option (P := fun J _ =>
      ∀ (W' : J → Type x) (F' : J → Type y) [∀ j, Fintype (W' j)] [∀ j, Fintype (F' j)]
        (r' : J → V) (H' : ∀ j, RootedGraph (W' j) (F' j)),
        (∀ j, (H' j).Planar) → (G.attachFamily r' H').Planar)
    · intro A B _ e ih W' F' _ _ r' H' hH'
      exact (attachFamilyReindex G e r' H').planar_iff.mp
        (ih (fun a => W' (e a)) (fun a => F' (e a)) (fun a => r' (e a))
          (fun a => H' (e a)) (fun a => hH' (e a)))
    · intro W' F' _ _ r' H' _
      exact (attachFamilyEmptyEquiv G r' H').planar_iff.mp hG
    · intro A _ ih W' F' _ _ r' H' hH'
      have hp := ih (fun a => W' (some a)) (fun a => F' (some a))
        (fun a => r' (some a)) (fun a => H' (some a)) (fun a => hH' (some a))
      exact (attachFamilyOptionEquiv G r' H').planar_iff.mp
        (hp.attachRooted (hH' none) (Sum.inl (r' none)))
  exact hgeneral I W F r H hH

end PlanarHom.MultiGraph
