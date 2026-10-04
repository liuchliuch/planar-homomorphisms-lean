import PlanarHom.PortPatchRotationRows

/-! The explicit finite vertex scan reduces to the single local row at any
known preimage whenever a patch's placement is injective. -/
noncomputable section
open Classical
namespace PlanarHom.PortPatchAssembly
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization

 theorem selectWord_eq {A B : Type} [DecidableEq A] (xs : List A) (hn:xs.Nodup) (w:A) (hw:w∈xs)
     (words:A→List B) : xs.flatMap (fun x=>if x=w then words x else [])=words w := by
   induction xs with
   | nil => simp at hw
   | cons x xs ih =>
     obtain ⟨hx,ht⟩:=List.nodup_cons.mp hn
     by_cases he:x=w
     · subst x
       have hh : xs.flatMap (fun x=>if x=w then words x else [])=[] := by
         apply List.flatMap_eq_nil_iff.mpr
         intro y hy
         have hne:y≠w := fun h=>hx (h ▸ hy)
         simp [hne]
       simp [hh]
     · have hm:w∈xs := (List.mem_cons.mp hw).resolve_left (Ne.symm he)
       simpa [he] using ih ht hm

 variable {C B : Type} {P W E : C→Type}
 variable (G : ∀c,MultiGraph (P c⊕W c) (E c)) (port : ∀c,P c→B)
 variable [∀c,DecidableEq (Dart (E c))] [DecidableEq (Dart (Sigma E))]
 variable (rows:∀c,RotationRows (G c)) (vertices:∀c,List (P c⊕W c))

 theorem localRowWord_preimage (c:C) (w:P c⊕W c)
     (hn:(vertices c).Nodup) (hw:w∈vertices c)
     (hinj:Function.Injective (placeVertex (W:=W) port c)) :
     localRowWord G port rows vertices c (placeVertex port c w)=(rows c).row w := by
   unfold localRowWord
   simp only [hinj.eq_iff]
   exact selectWord_eq _ hn w hw _
end PlanarHom.PortPatchAssembly
