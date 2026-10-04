import PlanarHom.RadialPottsTileCoordinates
import PlanarHom.RadialPottsTileSegmentAvoidance

/-! NEW occurrence-preserving map from the actual switched radial graph into
the proved integer segment model. -/
namespace PlanarHom.RadialPottsTileGeometry
open IntegerStraightDrawing RadialPottsTile
open RadialPottsTileCoordinates

/-- The original directed ring edge index, before the red endpoint switches. -/
def shortIndex {k : ℕ} (e : HalfShort k × Bool) : Fin (8*e.1.1.val+4) :=
  ⟨2*e.1.2.val+(if e.2 then 1 else 0),by have:=e.1.2.isLt; split_ifs <;> omega⟩
def shortWhite {k : ℕ} (e : HalfShort k × Bool) : White k := ⟨e.1.1,shortIndex e⟩

def edgeSegment {k : ℕ} : Edge k → Segment
  | .inl e => .long e.1.val e.2.1 e.2.2.val
  | .inr e =>
    let i := (shortIndex e).val
    let t := i%(2*e.1.1.val+1)
    let s := whiteSide (shortWhite e)
    if i=0 then .special e.1.1.val
    else if t<2*e.1.1.val then .side e.1.1.val s t
    else .corner e.1.1.val s

theorem edgeSegment_valid {k : ℕ} (e : Edge k) : (edgeSegment e).Valid k := by
  cases e with
  | inl e =>
    have := e.1.isLt
    have := e.2.2.isLt
    simp only [edgeSegment,Segment.Valid]
    omega
  | inr e =>
    have hr := e.1.1.isLt
    have hi := (shortIndex e).isLt
    have hm := Nat.mod_lt (shortIndex e).val (by omega : 0<2*e.1.1.val+1)
    simp only [edgeSegment]
    split_ifs with hz ht
    · simp only [Segment.Valid]; omega
    · simp only [Segment.Valid]
      refine ⟨by omega,by omega,by omega,by omega,?_⟩
      by_cases hs : whiteSide (shortWhite e)=0
      · right
        have hd := congrArg Fin.val hs
        dsimp [whiteSide,shortWhite] at hd
        have he := Nat.mod_add_div (shortIndex e).val (2*e.1.1.val+1)
        intro hzero
        have hzero' : (shortIndex e).val % (2*e.1.1.val+1)=0 := by exact_mod_cast hzero
        rw [hd,hzero'] at he
        simp only [Nat.mul_zero,Nat.zero_add] at he
        exact hz he.symm
      · exact Or.inl hs
    · simp only [Segment.Valid]
      refine ⟨by omega,by omega,?_⟩
      by_cases hs : whiteSide (shortWhite e)=0
      · right
        intro hr0
        have hr0' : e.1.1.val=0 := by exact_mod_cast hr0
        have hd := congrArg Fin.val hs
        simp [whiteSide,shortWhite,hr0'] at hd
        exact hz (congrArg Fin.val hd)
      · exact Or.inl hs

/-- A proof-independent tag that retains the original occurrence identity. -/
def Segment.code : Segment → Bool × ℤ × ℤ × ℤ
  | .long r s a => (false,r,s.val,a)
  | .side r s t => (true,r,s.val*(2*r+1)+t,0)
  | .corner r s => (true,r,s.val*(2*r+1)+2*r,0)
  | .special r => (true,r,0,0)

def edgeCode {k : ℕ} : Edge k → Bool × ℤ × ℤ × ℤ
  | .inl e => (false,e.1.val,e.2.1.val,e.2.2.val)
  | .inr e => (true,e.1.1.val,(shortIndex e).val,0)

theorem edgeSegment_code {k : ℕ} (e : Edge k) : (edgeSegment e).code=edgeCode e := by
  cases e with
  | inl e => rfl
  | inr e =>
    have hm := Nat.mod_lt (shortIndex e).val (by omega : 0<2*e.1.1.val+1)
    have hid := Nat.div_add_mod (shortIndex e).val (2*e.1.1.val+1)
    simp only [edgeSegment]
    split_ifs with hz ht
    · simp [Segment.code,edgeCode,hz]
    · simp only [Segment.code,edgeCode,whiteSide,shortWhite]
      congr 3
      exact_mod_cast (by simpa [Nat.mul_comm] using hid : _ = (shortIndex e).val)
    · simp only [Segment.code,edgeCode,whiteSide,shortWhite]
      have hmod : (shortIndex e).val % (2*e.1.1.val+1)=2*e.1.1.val := by omega
      rw [hmod] at hid
      congr 3
      exact_mod_cast (by simpa [Nat.mul_comm] using hid : _ = (shortIndex e).val)

 theorem edgeCode_injective {k : ℕ} : Function.Injective (@edgeCode k) := by
  intro e f he
  cases e with
  | inl e =>
    cases f with
    | inr f => simp [edgeCode] at he
    | inl f =>
      have hh : e.1=f.1 ∧ e.2.1=f.2.1 ∧ e.2.2.val=f.2.2.val := by
        simp only [edgeCode,Prod.mk.injEq] at he
        exact ⟨Fin.ext (by omega),Fin.ext (by omega),by omega⟩
      apply congrArg Sum.inl
      rcases e with ⟨r,s,a⟩
      rcases f with ⟨q,t,b⟩
      dsimp at hh
      obtain ⟨hr,hs,ha⟩ := hh
      subst q; subst t
      have hab:a=b := Fin.ext ha
      subst b
      rfl
  | inr e =>
    cases f with
    | inl f => simp [edgeCode] at he
    | inr f =>
      have hh : e.1.1=f.1.1 ∧ (shortIndex e).val=(shortIndex f).val := by
        simp only [edgeCode,Prod.mk.injEq] at he
        exact ⟨Fin.ext (by omega),by omega⟩
      apply congrArg Sum.inr
      rcases e with ⟨⟨r,a⟩,b⟩
      rcases f with ⟨⟨q,c⟩,d⟩
      obtain ⟨hr,hi⟩ := hh
      dsimp at hr
      subst q
      have hd : b=d := by cases b <;> cases d <;> simp [shortIndex] at hi ⊢ <;> omega
      subst d
      have hac : a=c := by apply Fin.ext; cases b <;> simp [shortIndex] at hi <;> omega
      subst c
      rfl

theorem edgeSegment_injective {k : ℕ} : Function.Injective (@edgeSegment k) := by
  intro e f he
  apply edgeCode_injective
  rw [←edgeSegment_code,←edgeSegment_code,he]

end PlanarHom.RadialPottsTileGeometry
