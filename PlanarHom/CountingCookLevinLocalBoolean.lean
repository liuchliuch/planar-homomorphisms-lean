import PlanarHom.CountingCookLevinLocalKernel

/-! Fixed finite NOR templates for the concrete tape-machine local kernel.
Only eleven local fields are matched. Global configurations are never enumerated. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic

/-- One-hot test inputs for the fixed local context fields. -/
inductive LocalBit (m : Machine) where
  | control (q : Control m.Q)
  | head (a : m.Γ)
  | choice (b : Bool)
  | valid (b : Bool)
  | leftHead (a : Option m.Γ)
  | rightHead (a : Option m.Γ)
  | previous (a : Option m.Γ)
  | current (a : Option m.Γ)
  | next (a : Option m.Γ)
  | first (b : Bool)
  | leftSide (b : Bool)
  deriving Fintype

def contextBits (m : Machine) (c : LocalContext m) : LocalBit m → Bool
  | .control q => decide (c.control=q)
  | .head a => decide (c.head=a)
  | .choice b => decide (c.choice=b)
  | .valid b => decide (c.valid=b)
  | .leftHead a => decide (c.leftHead=a)
  | .rightHead a => decide (c.rightHead=a)
  | .previous a => decide (c.previous=a)
  | .current a => decide (c.current=a)
  | .next a => decide (c.next=a)
  | .first b => decide (c.first=b)
  | .leftSide b => decide (c.leftSide=b)

def contextTests (m : Machine) (a : LocalContext m) : List (LocalBit m) :=
  [.control a.control,.head a.head,.choice a.choice,.valid a.valid,
   .leftHead a.leftHead,.rightHead a.rightHead,.previous a.previous,.current a.current,
   .next a.next,.first a.first,.leftSide a.leftSide]

def matchContext (m : Machine) (a : LocalContext m) : Expr (LocalBit m ⊕ Bool) :=
  Expr.allExpr ((contextTests m a).map (fun t => Expr.var (.inl t)))

/-- Every tested context has exactly the listed eleven concrete field tests. -/
theorem eval_matchContext (m : Machine) (a c : LocalContext m) :
    (matchContext m a).eval (Expr.grounded (contextBits m c))=decide (c=a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [matchContext,Expr.eval_allExpr,List.all_eq_true,List.mem_map,decide_eq_true_eq]
  constructor
  · intro h
    have htest (t : LocalBit m) (ht : t∈contextTests m a) : contextBits m c t=true :=
      h _ ⟨t,ht,rfl⟩
    have hfields : c.control=a.control ∧ c.head=a.head ∧ c.choice=a.choice ∧ c.valid=a.valid ∧
        c.leftHead=a.leftHead ∧ c.rightHead=a.rightHead ∧ c.previous=a.previous ∧
        c.current=a.current ∧ c.next=a.next ∧ c.first=a.first ∧ c.leftSide=a.leftSide := by
      simpa [contextTests,contextBits] using htest
    cases a
    cases c
    simp_all
  · rintro rfl e ⟨t,ht,rfl⟩
    have : contextBits m c t=true := by
      simp only [contextTests,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [contextBits]
    exact this

/-- A source-machine-fixed Boolean template for any one local output bit. -/
def localTemplate (m : Machine) (f : LocalContext m → Bool) : Expr (LocalBit m ⊕ Bool) :=
  Expr.anyExpr (((Finset.univ.filter (fun c => f c=true)).toList).map (matchContext m))

theorem localTemplate_correct (m : Machine) (f : LocalContext m → Bool) (c : LocalContext m) :
    (localTemplate m f).eval (Expr.grounded (contextBits m c))=f c := by
  apply Bool.eq_iff_iff.mpr
  simp only [localTemplate,Expr.eval_anyExpr,List.any_eq_true,List.mem_map]
  constructor
  · rintro ⟨e,⟨a,ha,rfl⟩,he⟩
    have hc : c=a := by simpa only [eval_matchContext,decide_eq_true_eq] using he
    subst c
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp ha)).2
  · intro h
    exact ⟨matchContext m c,⟨c,Finset.mem_toList.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩),rfl⟩,by simp [eval_matchContext]⟩

/-- Reindex fixed local inputs for the honest numeric NOR emitter. -/
def numericLocalTemplate (m : Machine) (f : LocalContext m → Bool) :
    Expr (Fin (Fintype.card (LocalBit m ⊕ Bool))) :=
  (localTemplate m f).rename (Fintype.equivFin (LocalBit m ⊕ Bool))

theorem fp_numericLocalTemplate (m : Machine) (f : LocalContext m → Bool) :
    Complexity.FP (templateInputEncoding (Fintype.card (LocalBit m ⊕ Bool)))
      ((Complexity.BitEncoding.nat.prod Complexity.BitEncoding.nat).list.prod Complexity.BitEncoding.nat)
      (fun p => ((numericLocalTemplate m f).emit p.1 p.2,
        (numericLocalTemplate m f).output p.1 p.2)) := Expr.fp_compile _

/-- These fixed NOR templates compute actual next control/head/validity bits,
with the local-kernel identities discharged, rather than assumed. -/
theorem local_step_bits (m : Machine) {L : ℕ} (s : ReplayState m L)
    (b side : Bool) (i : Fin (L+1)) (q : Control m.Q) (a : m.Γ) :
    (localTemplate m (fun c => decide (localControl m c=q))).eval
        (Expr.grounded (contextBits m (contextAt m s b side i))) = decide ((windowStep m s b).1.1.1=q) ∧
    (localTemplate m (fun c => decide (localHead m c=a))).eval
        (Expr.grounded (contextBits m (contextAt m s b side i))) = decide ((windowStep m s b).1.1.2=a) ∧
    (localTemplate m (localValid m)).eval
        (Expr.grounded (contextBits m (contextAt m s b side i))) = (windowStep m s b).2 := by
  simp only [localTemplate_correct]
  have h := windowStep_local_controls m s b side i
  rw [h.1,h.2.1,h.2.2]
  exact ⟨rfl,rfl,rfl⟩

theorem local_step_cell_bit (m : Machine) {L : ℕ} (s : ReplayState m L)
    (b side : Bool) (i : Fin (L+1)) (a : Option m.Γ) :
    (localTemplate m (fun c => decide (localCell m c=a))).eval
        (Expr.grounded (contextBits m (contextAt m s b side i))) =
      decide ((if side then (windowStep m s b).1.2.1 else (windowStep m s b).1.2.2) i=a) := by
  rw [localTemplate_correct,windowStep_local_cell]

end PlanarHom.CountingCookLevin
