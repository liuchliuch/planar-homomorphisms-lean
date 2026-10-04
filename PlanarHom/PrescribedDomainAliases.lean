import PlanarHom.MixedRelabelSemantics
import PlanarHom.PrescribedDomainTyping

/-! # Exact finite-label aliases with unchanged prescribed vertex domains -/
namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode FiniteLabelLookupMachines
variable {a b d bt : ℕ}

/-- Ordinary labels follow ρ; reserved intrinsic indicators keep their domain
index and move only by the new ordinary-language offset. -/
def liftUnaryAlias (ρ : Fin a→Fin b) (d : ℕ) : Fin (a+d)→Fin (b+d) :=
  Fin.addCases (fun i => Fin.castAdd d (ρ i)) (fun j => Fin.natAdd b j)

@[simp] theorem liftUnaryAlias_regular (ρ : Fin a→Fin b) (i : Fin a) :
    liftUnaryAlias ρ d (Fin.castAdd d i)=Fin.castAdd d (ρ i) := Fin.addCases_left _

@[simp] theorem liftUnaryAlias_reserved (ρ : Fin a→Fin b) (i : Fin d) :
    liftUnaryAlias ρ d (Fin.natAdd a i)=Fin.natAdd b i := Fin.addCases_right _

theorem lookup_lift_regular (ρ : Fin a→Fin b) (i : Fin a) :
    lookup (finTable (liftUnaryAlias ρ d)) i.val=(ρ i).val := by
  change lookup (finTable (liftUnaryAlias ρ d)) (Fin.castAdd d i).val=_
  rw [lookup_finTable,liftUnaryAlias_regular]
  rfl

theorem lookup_lift_reserved (ρ : Fin a→Fin b) (i : Fin d) :
    lookup (finTable (liftUnaryAlias ρ d)) (a+i.val)=b+i.val := by
  change lookup (finTable (liftUnaryAlias ρ d)) (Fin.natAdd a i).val=_
  rw [lookup_finTable,liftUnaryAlias_reserved]
  rfl

/-- Binary relabeling changes no unary/domain metadata. -/
theorem relabelBinary_withDomains (ρ : Fin a→Fin b) {ut : ℕ} (g : MixedCode)
    (δ : Fin g.vertices→Fin d) :
    (withDomains (unaryTypes:=ut) g δ).relabelBinary (finTable ρ)=
      withDomains (unaryTypes:=ut) (g.relabelBinary (finTable ρ)) δ := rfl

/-- Unary aliases move the reserved label offset while preserving exactly δ. -/
theorem relabelUnary_withDomains (ρ : Fin a→Fin b) (g : MixedCode) (hg : g.Valid bt a)
    (δ : Fin g.vertices→Fin d) :
    (withDomains (unaryTypes:=a) g δ).relabelUnary (finTable (liftUnaryAlias ρ d))=
      withDomains (unaryTypes:=b) (g.relabelUnary (finTable ρ)) δ := by
  simp only [relabelUnary,withDomains,domainOccurrences,List.map_append,List.map_ofFn]
  congr 1
  apply congrArg₂ List.append
  · apply List.map_congr_left
    intro u hu
    have hi := (hg.2 u hu).2
    rw [lookup_lift_regular ρ ⟨u.2,hi⟩,lookup_finTable ρ ⟨u.2,hi⟩]
  · apply congrArg List.ofFn
    funext v
    dsimp only [Function.comp_apply]
    rw [lookup_lift_reserved]

/-- Fixed endpoint-domain compatibility is the only typing requirement. The
original vertex-domain assignment and ordered occurrence endpoints remain. -/
theorem Typed.relabelBinaryAlias (ρ : Fin a→Fin b) {ut : ℕ}
    {BT : Fin a→Fin d→Fin d→Prop} {BS : Fin b→Fin d→Fin d→Prop} {U : Fin ut→Fin d→Prop}
    (hB : ∀i x y,BT i x y→BS (ρ i) x y)
    {g : MixedCode} {hg : g.Valid a ut} {δ : Fin g.vertices→Fin d} (h : Typed BT U g hg δ) :
    Typed BS U (g.relabelBinary (finTable ρ)) (relabelBinary_valid _ hg (lookup_finTable_lt ρ)) δ := by
  refine ⟨?_,h.2⟩
  intro e he
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp he
  have hlabel : (⟨lookup (finTable ρ) old.2.2,lookup_finTable_lt ρ _ (hg.1 old hold).2.2⟩ : Fin b)=
      ρ ⟨old.2.2,(hg.1 old hold).2.2⟩ := Fin.ext (lookup_finTable ρ ⟨old.2.2,(hg.1 old hold).2.2⟩)
  simpa only [hlabel] using hB _ _ _ (h.1 old hold)

theorem Typed.relabelUnaryAlias (ρ : Fin a→Fin b)
    {B : Fin bt→Fin d→Fin d→Prop} {UT : Fin a→Fin d→Prop} {US : Fin b→Fin d→Prop}
    (hU : ∀i x,UT i x→US (ρ i) x)
    {g : MixedCode} {hg : g.Valid bt a} {δ : Fin g.vertices→Fin d} (h : Typed B UT g hg δ) :
    Typed B US (g.relabelUnary (finTable ρ)) (relabelUnary_valid _ hg (lookup_finTable_lt ρ)) δ := by
  refine ⟨h.1,?_⟩
  intro u hu
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hu
  have hlabel : (⟨lookup (finTable ρ) old.2,lookup_finTable_lt ρ _ (hg.2 old hold).2⟩ : Fin b)=
      ρ ⟨old.2,(hg.2 old hold).2⟩ := Fin.ext (lookup_finTable ρ ⟨old.2,(hg.2 old hold).2⟩)
  simpa only [hlabel] using hU _ _ (h.2 old hold)

section Values
variable {C R : Type} [CommSemiring R]

theorem extendedUnaries_comp_alias (ρ : Fin a→Fin b) (U : Fin b→C→R) (D : Fin d→Set C) :
    extendedUnaries U D ∘ liftUnaryAlias ρ d=extendedUnaries (U ∘ ρ) D := by
  funext i c
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Function.comp_apply,liftUnaryAlias,extendedUnaries,Fin.addCases_left]
  · simp [Function.comp_apply,liftUnaryAlias,extendedUnaries,Fin.addCases_right]

end Values
end PlanarHom.PrescribedDomains

namespace PlanarHom.FiniteLanguageAliases

/-- Append one auxiliary label after every existing label, preserving companions. -/
def appendOne {α : Type} {n : ℕ} (F : Fin n→α) (x : α) : Fin (n+1)→α :=
  Fin.addCases F (fun _ : Fin 1 => x)

/-- Only the last auxiliary label is merged into one specified existing label. -/
def aliasAux {n : ℕ} (old : Fin n) : Fin (n+1)→Fin n := Fin.addCases id (fun _ : Fin 1 => old)

@[simp] theorem appendOne_old {α : Type} {n : ℕ} (F : Fin n→α) (x : α) (i : Fin n) :
    appendOne F x (Fin.castAdd 1 i)=F i := Fin.addCases_left _

@[simp] theorem appendOne_aux {α : Type} {n : ℕ} (F : Fin n→α) (x : α) :
    appendOne F x (Fin.last n)=x := by
  change appendOne F x (Fin.natAdd n (0 : Fin 1))=x
  exact Fin.addCases_right _

@[simp] theorem aliasAux_old {n : ℕ} (old i : Fin n) : aliasAux old (Fin.castAdd 1 i)=i := Fin.addCases_left _

@[simp] theorem aliasAux_aux {n : ℕ} (old : Fin n) : aliasAux old (Fin.last n)=old := by
  change aliasAux old (Fin.natAdd n (0 : Fin 1))=old
  exact Fin.addCases_right _

theorem comp_aliasAux {α : Type} {n : ℕ} (F : Fin n→α) (old : Fin n) :
    F ∘ aliasAux old=appendOne F (F old) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Function.comp_apply]
  · simp [Function.comp_apply,aliasAux,appendOne,Fin.addCases_right]

/-- For F∪{C,C'}, only C' is sent to the already present C label. -/
def aliasSecond {n : ℕ} : Fin ((n+1)+1)→Fin (n+1) := aliasAux (Fin.last n)

@[simp] theorem aliasSecond_companion {n : ℕ} (i : Fin n) :
    aliasSecond (Fin.castAdd 1 (Fin.castAdd 1 i))=Fin.castAdd 1 i := aliasAux_old _ _

@[simp] theorem aliasSecond_old {n : ℕ} : aliasSecond (Fin.castAdd 1 (Fin.last n))=Fin.last n := aliasAux_old _ _

@[simp] theorem aliasSecond_aux {n : ℕ} : aliasSecond (Fin.last (n+1))=Fin.last n := aliasAux_aux _

theorem appendOne_comp_aliasSecond {α : Type} {n : ℕ} (F : Fin n→α) (C : α) :
    appendOne F C ∘ aliasSecond=appendOne (appendOne F C) C := by
  rw [aliasSecond,comp_aliasAux,appendOne_aux]

end PlanarHom.FiniteLanguageAliases
