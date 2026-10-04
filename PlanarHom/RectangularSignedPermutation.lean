import PlanarHom.RectangularOrthogonalDegrees

/-! NEW exact coordinate permutation forced by disjoint orthogonal row supports.
Its signs are realized by genuine Boolean color flips. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

def signValue (b:Bool):ℝ:=if b then -1 else 1

theorem orthogonal_disjoint_signed_permutation (U:Matrix (Fin d) (Fin d) ℝ)
    (hU:U*U.transpose=1) (hdisj:∀i k,i≠k→∀j,U i j*U k j=0) :
    ∃p:Fin d≃Fin d,∃flip:Fin d→Bool,∀i j,U i j=if j=p i then signValue (flip i) else 0 := by
  choose col hcol using orthogonal_row_nonzero U hU
  have hinj:Function.Injective col:=by
    intro i k he
    by_contra hik
    have hz:=hdisj i k hik (col i)
    rw [he] at hz
    exact (mul_ne_zero (by simpa only [he] using hcol i) (hcol k)) hz
  let p:Fin d≃Fin d:=Equiv.ofBijective col ⟨hinj,Finite.surjective_of_injective hinj⟩
  have hzero:∀i j,j≠p i→U i j=0:=by
    intro i j hne
    let k:=p.symm j
    have hki:k≠i:=by
      intro he
      have h:=p.apply_symm_apply j
      change p k=j at h
      rw [he] at h
      exact hne h.symm
    have hz:=hdisj i k hki.symm j
    exact (mul_eq_zero.mp hz).resolve_right (by
      have h:=hcol k
      have hk:p k=j:=p.apply_symm_apply j
      simpa only [show col k=p k from rfl,hk] using h)
  have hsquare:∀i,U i (p i)^2=1:=by
    intro i
    have hi:=congrFun (congrFun hU i) i
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq] at hi
    have he:(∑j,U i j*U i j)=U i (p i)*U i (p i):=by
      apply Finset.sum_eq_single (p i)
      · intro j _ hj
        rw [hzero i j hj,zero_mul]
      · simp
    rw [he] at hi
    simpa only [pow_two] using hi
  have hsign:∀i,∃f:Bool,U i (p i)=signValue f:=by
    intro i
    rcases sq_eq_one_iff.mp (hsquare i) with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  choose flip hflip using hsign
  refine ⟨p,flip,?_⟩
  intro i j
  by_cases hj:j=p i
  · subst j
    simp only [if_true,hflip]
  · simp only [hj,if_false,hzero i j hj]

def signedColorEquiv (p:Fin d≃Fin d) (flip:Fin d→Bool):Cube d≃Cube d where
  toFun:=fun y i=>Bool.xor (flip i) (y (p i))
  invFun:=fun y j=>Bool.xor (flip (p.symm j)) (y (p.symm j))
  left_inv:=by
    intro y
    funext j
    simp [Bool.xor_assoc]
  right_inv:=by
    intro y
    funext i
    simp [Bool.xor_assoc]

theorem signedColor_single_character (p:Fin d≃Fin d) (flip:Fin d→Bool)
    (i:Fin d) (y:Cube d) :
    bitCharacter true (signedColorEquiv p flip y i)=signValue (flip i)*bitCharacter true (y (p i)) := by
  change bitCharacter true (Bool.xor (flip i) (y (p i)))=_
  have hb (x z:Bool):bitCharacter true (Bool.xor x z)=signValue x*bitCharacter true z:=by
    cases x <;> cases z <;> norm_num [bitCharacter,signValue]
  exact hb _ _

end PlanarHom.RectangularWalshConvolution
