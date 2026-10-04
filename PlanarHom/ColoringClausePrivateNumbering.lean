import PlanarHom.ColoringClausePaletteState

/-! Explicit contiguous numbering of the 102 non-primary vertices of a clause.
The map is arithmetic and retains the actual palette and internal vertices; it
is not a cardinality-only reindexing chosen by a finite enumeration oracle. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarColoringClause
set_option maxHeartbeats 5000000


def Primary (v : Vertex) : Prop := v=0 ∨ v=34 ∨ v=68
instance (v : Vertex) : Decidable (Primary v) := by unfold Primary; infer_instance
abbrev PrivateVertex := {v : Vertex // ¬Primary v}

def paletteVertex (p : Fin 3 × Bool) : Vertex :=
  if p.2 then boundary (grayPort p.1) else boundary (blackPort p.1)

theorem paletteVertex_injective : Function.Injective paletteVertex := by decide

theorem paletteVertex_private : ∀ p,¬Primary (paletteVertex p) := by decide

theorem paletteVertex_port (p : Fin 3 × Bool) : IsPort (paletteVertex p) := by
  cases hp : p.2
  · exact ⟨blackPort p.1,by simp [paletteVertex,hp]⟩
  · exact ⟨grayPort p.1,by simp [paletteVertex,hp]⟩

theorem primary_port (v : Vertex) (h : Primary v) : IsPort v := by
  rcases h with rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨6,rfl⟩

def privatePartsMap : (Fin 3 × Bool) ⊕ InternalVertex → PrivateVertex
  | .inl p => ⟨paletteVertex p,paletteVertex_private p⟩
  | .inr v => ⟨v.val,fun h => v.property (primary_port v.val h)⟩

def privatePartsEquiv : ((Fin 3 × Bool) ⊕ InternalVertex) ≃ PrivateVertex :=
  Equiv.ofBijective privatePartsMap ⟨by
    intro a b he
    have hv := congrArg Subtype.val he
    rcases a with p | v <;> rcases b with q | w
    · exact congrArg Sum.inl (paletteVertex_injective hv)
    · exact False.elim (w.property (hv ▸ paletteVertex_port p))
    · exact False.elim (v.property (hv.symm ▸ paletteVertex_port q))
    · exact congrArg Sum.inr (Subtype.ext hv),by
    intro v
    by_cases hp : IsPort v.val
    · obtain ⟨k,hk⟩ := hp
      have hv : ¬Primary (boundary k) := hk ▸ v.property
      fin_cases k
      · exact False.elim (hv (Or.inl rfl))
      · exact ⟨.inl (0,false),Subtype.ext hk⟩
      · exact ⟨.inl (0,true),Subtype.ext hk⟩
      · exact False.elim (hv (Or.inr (Or.inl rfl)))
      · exact ⟨.inl (1,false),Subtype.ext hk⟩
      · exact ⟨.inl (1,true),Subtype.ext hk⟩
      · exact False.elim (hv (Or.inr (Or.inr rfl)))
      · exact ⟨.inl (2,false),Subtype.ext hk⟩
      · exact ⟨.inl (2,true),Subtype.ext hk⟩
    · exact ⟨.inr ⟨v.val,hp⟩,Subtype.ext rfl⟩⟩

def compress (v : Vertex) : ℕ :=
  if v.val<34 then v.val-1 else if v.val<68 then v.val-2 else v.val-3

def expand (i : Fin 102) : ℕ :=
  if i.val<33 then i.val+1 else if i.val<66 then i.val+2 else i.val+3

def privateNumber (v : PrivateVertex) : Fin 102 := ⟨compress v.val,by
  have h := v.val.isLt
  unfold compress
  split <;> (try split) <;> omega⟩

def privateUnnumber (i : Fin 102) : PrivateVertex :=
  ⟨⟨expand i,by unfold expand; split <;> (try split) <;> have := i.isLt <;> omega⟩,by
    intro hp
    rcases hp with hp | hp | hp
    all_goals have he := congrArg Fin.val hp
    all_goals norm_num at he
    all_goals unfold expand at he
    all_goals split at he <;> (try split at he) <;> omega⟩

theorem privateNumber_inverse (i : Fin 102) : privateNumber (privateUnnumber i)=i := by
  apply Fin.ext
  change (if expand i<34 then expand i-1 else if expand i<68 then expand i-2 else expand i-3)=i.val
  unfold expand
  split_ifs <;> omega

theorem privateUnnumber_inverse (v : PrivateVertex) : privateUnnumber (privateNumber v)=v := by
  apply Subtype.ext
  apply Fin.ext
  have h0 : v.val.val≠0 := fun h => v.property (Or.inl (Fin.ext h))
  have h34 : v.val.val≠34 := fun h => v.property (Or.inr (Or.inl (Fin.ext h)))
  have h68 : v.val.val≠68 := fun h => v.property (Or.inr (Or.inr (Fin.ext h)))
  change (if compress v.val<33 then compress v.val+1 else if compress v.val<66 then compress v.val+2 else compress v.val+3)=v.val.val
  unfold compress
  split_ifs <;> omega

def privateNumberEquiv : PrivateVertex ≃ Fin 102 where
  toFun := privateNumber
  invFun := privateUnnumber
  left_inv := privateUnnumber_inverse
  right_inv := privateNumber_inverse

/-- The concrete palette/internal block map consumed by the numeric compiler. -/
def privateIndex : ((Fin 3 × Bool) ⊕ InternalVertex) ≃ Fin 102 :=
  privatePartsEquiv.trans privateNumberEquiv

end PlanarHom.PlanarColoringClause
