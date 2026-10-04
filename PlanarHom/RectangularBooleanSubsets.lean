import PlanarHom.RectangularWalshPolynomials
import Mathlib.Data.Finset.Powerset

/-! NEW literal subset interpretation of Boolean Fourier indices and exact
counting of the minimum-degree ordered decompositions of a target character. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

def bitSupport (S:Cube d):Finset (Fin d):=Finset.univ.filter (fun i=>S i)
def bitsOfSet (s:Finset (Fin d)):Cube d:=fun i=>decide (i∈s)

@[simp] theorem mem_bitSupport (S:Cube d) (i:Fin d):i∈bitSupport S↔S i=true:=by simp [bitSupport]
@[simp] theorem bitsOfSet_support (S:Cube d):bitsOfSet (bitSupport S)=S:=by
  funext i
  simp [bitsOfSet]
@[simp] theorem support_bitsOfSet (s:Finset (Fin d)):bitSupport (bitsOfSet s)=s:=by
  ext i
  simp [bitsOfSet]

def bitSetEquiv (d:ℕ):Cube d≃Finset (Fin d) where
  toFun:=bitSupport
  invFun:=bitsOfSet
  left_inv:=bitsOfSet_support
  right_inv:=support_bitsOfSet

theorem degree_eq_support_card (S:Cube d):Boolean.degree S=(bitSupport S).card:=by
  simp [Boolean.degree,bitSupport,Finset.sum_boole]

theorem degree_zero_iff (S:Cube d):Boolean.degree S=0↔S=fun _=>false:=by
  rw [degree_eq_support_card,Finset.card_eq_zero]
  constructor
  · intro h
    funext i
    have hi:i∉bitSupport S:=by rw [h];simp
    simpa using hi
  · intro h
    simp [h,bitSupport]

theorem minimal_split_iff (S I:Cube d):
    Boolean.degree I+Boolean.degree (xor S I)=Boolean.degree S↔bitSupport I⊆bitSupport S:=by
  have hadd:=degree_xor_add I (xor S I)
  have hxor:xor I (xor S I)=S:=by funext i;simp [Boolean.xor,Bool.xor_comm,Bool.xor_left_comm]
  rw [hxor] at hadd
  have hz:Boolean.degree I+Boolean.degree (xor S I)=Boolean.degree S↔
      intersectBits I (xor S I)=fun _=>false:=by
    rw [←degree_zero_iff]
    omega
  rw [hz]
  constructor
  · intro he i hi
    have hv:=congrFun he i
    have hi':I i=true:=mem_bitSupport I i|>.mp hi
    simp only [intersectBits,Boolean.xor,hi',Bool.true_and] at hv
    simpa using hv
  · intro h
    funext i
    have hi:(I i=true)→S i=true:=fun hi=>mem_bitSupport S i|>.mp (h (mem_bitSupport I i|>.mpr hi))
    have hb (x y:Bool) (h:(y=true)→x=true):(y && Bool.xor x y)=false:=by
      cases x <;> cases y <;> simp_all
    exact hb (S i) (I i) hi

def splitEquivPowerset (S:Cube d):
    {I:Cube d // Boolean.degree I+Boolean.degree (xor S I)=Boolean.degree S}≃
      ↥((bitSupport S).powerset) where
  toFun:=fun I=>⟨bitSupport I.val,Finset.mem_powerset.mpr ((minimal_split_iff S I.val).mp I.property)⟩
  invFun:=fun s=>⟨bitsOfSet s.val,(minimal_split_iff S _).mpr (by
    rw [support_bitsOfSet]
    exact Finset.mem_powerset.mp s.property)⟩
  left_inv:=by intro I;apply Subtype.ext;exact bitsOfSet_support I.val
  right_inv:=by intro s;apply Subtype.ext;exact support_bitsOfSet s.val

theorem count_minimal_splits (S:Cube d):
    Fintype.card {I:Cube d // Boolean.degree I+Boolean.degree (xor S I)=Boolean.degree S}=2^(Boolean.degree S):=by
  rw [Fintype.card_congr (splitEquivPowerset S)]
  simp only [Fintype.card_coe,Finset.card_powerset,degree_eq_support_card]

theorem xor_eq_zero_iff (S T:Cube d):xor S T=(fun _=>false)↔S=T:=by
  constructor
  · intro h
    funext i
    have hi:=congrFun h i
    have hb (x y:Bool):(Bool.xor x y=false)→x=y:=by cases x <;> cases y <;> decide
    exact hb (S i) (T i) hi
  · rintro rfl
    funext i
    simp [Boolean.xor]

@[simp] theorem xor_zero_right (S:Cube d):xor S (fun _=>false)=S:=by funext i;simp [Boolean.xor]
@[simp] theorem xor_zero_left (S:Cube d):xor (fun _=>false) S=S:=by funext i;simp [Boolean.xor]
@[simp] theorem xor_self_zero (S:Cube d):xor S S=(fun _=>false):=by funext i;simp [Boolean.xor]


end PlanarHom.RectangularWalshConvolution
