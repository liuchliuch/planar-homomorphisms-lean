import PlanarHom.UnaryLoopRealization
import PlanarHom.PrescribedDomainAliases

/-! A concrete finite permutation moves the appended ordinary unary past the
reserved domain records before the actual loop-realization machine runs. -/
noncomputable section
open Classical
namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode FiniteLanguageAliases FiniteLabelLookupMachines

def auxUnaryLast (u d : ℕ) : Fin (u+1+d)→Fin (u+d+1) :=
  Fin.addCases
    (Fin.lastCases (Fin.last (u+d)) (fun i=>Fin.castAdd 1 (Fin.castAdd d i)))
    (fun k=>Fin.castAdd 1 (Fin.natAdd u k))

@[simp] theorem auxUnaryLast_old (u d : ℕ) (i : Fin u) :
    auxUnaryLast u d (Fin.castAdd d (Fin.castAdd 1 i))=Fin.castAdd 1 (Fin.castAdd d i) := by
  simp only [auxUnaryLast,Fin.addCases_left]
  change Fin.lastCases (motive:=fun _=>Fin (u+d+1)) (Fin.last (u+d))
    (fun j=>Fin.castAdd 1 (Fin.castAdd d j)) i.castSucc = _
  rw [Fin.lastCases_castSucc]

@[simp] theorem auxUnaryLast_aux (u d : ℕ) :
    auxUnaryLast u d (Fin.castAdd d (Fin.last u))=Fin.last (u+d) := by
  simp [auxUnaryLast]

@[simp] theorem auxUnaryLast_domain (u d : ℕ) (i : Fin d) :
    auxUnaryLast u d (Fin.natAdd (u+1) i)=Fin.castAdd 1 (Fin.natAdd u i) := by
  simp [auxUnaryLast]

theorem lookup_auxUnaryLast_old {u d n : ℕ} (hn : n<u) :
    lookup (finTable (auxUnaryLast u d)) n=n := by
  have h := lookup_finTable (auxUnaryLast u d) (Fin.castAdd d (Fin.castAdd 1 ⟨n,hn⟩))
  simpa only [auxUnaryLast_old,Fin.coe_castAdd] using h

@[simp] theorem lookup_auxUnaryLast_aux (u d : ℕ) :
    lookup (finTable (auxUnaryLast u d)) u=u+d := by
  have h := lookup_finTable (auxUnaryLast u d) (Fin.castAdd d (Fin.last u))
  simpa only [auxUnaryLast_aux,Fin.coe_castAdd,Fin.val_last] using h

theorem lookup_auxUnaryLast_domain (u d : ℕ) (k : Fin d) :
    lookup (finTable (auxUnaryLast u d)) (u+1+k.val)=u+k.val := by
  have h := lookup_finTable (auxUnaryLast u d) (Fin.natAdd (u+1) k)
  simpa only [auxUnaryLast_domain,Fin.coe_castAdd,Fin.coe_natAdd] using h

theorem extendedUnaries_auxUnaryLast {C R : Type} [CommSemiring R]
    {u d : ℕ} (U : Fin u→C→R) (v : C→R) (D : Fin d→Set C) :
    (appendOne (extendedUnaries U D) v) ∘ auxUnaryLast u d=extendedUnaries (appendOne U v) D := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun k=>?_) i
  · refine Fin.lastCases ?_ (fun l=>?_) j
    · simp only [Function.comp_apply,auxUnaryLast_aux,appendOne_aux,extendedUnaries,Fin.addCases_left]
    · change appendOne (extendedUnaries U D) v (auxUnaryLast u d (Fin.castAdd d (Fin.castAdd 1 l))) =
        extendedUnaries (appendOne U v) D (Fin.castAdd d (Fin.castAdd 1 l))
      simp only [auxUnaryLast_old,appendOne_old,extendedUnaries,Fin.addCases_left]
  · simp only [Function.comp_apply,auxUnaryLast_domain,appendOne_old,extendedUnaries,Fin.addCases_right]

end PlanarHom.PrescribedDomains
