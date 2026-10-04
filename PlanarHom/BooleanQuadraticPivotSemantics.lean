import PlanarHom.BooleanQuadraticFormMasks

/-! NEW semantic correctness of the literal dense pair elimination. -/
namespace PlanarHom.BooleanQuadratic
open scoped BigOperators

 theorem gauss_pivot {K : Type*} [CommRing K] {n : ℕ}
    (q : Data) (hn : dimension q=n) (i j : Fin n) (hij:j≠i)
    (hp : cross q i.val j.val=true) :
    2*gauss (K:=K) n q=gauss n (pivot q i.val j.val) := by
  classical
  let t : Finset (Fin n):=(Finset.univ.erase i).erase j
  let l : Fin n→F₂:=fun k=>bit (rawLinear q k.val)
  let m : Fin n→Fin n→F₂:=fun k r=>bit (entry q k.val r.val)
  let aa : Fin n→F₂:=fun k=>bit (cross q i.val k.val)
  let bb : Fin n→F₂:=fun k=>bit (cross q j.val k.val)
  let A := fun z=>affine t (bit (linear q i.val)) aa (extendPair i j z)
  let B := fun z=>affine t (bit (linear q j.val)) bb (extendPair i j z)
  let C := fun z=>form t (bit q.1) l m (extendPair i j z)
  have hC (x:Fin n→F₂) : C (fun k=>x k.val)=form t (bit q.1) l m x :=
    form_congr_on t _ _ _ _ _ (fun k hk=>extendPair_restrict Finset.univ i j x k hk)
  have hA (x:Fin n→F₂) : A (fun k=>x k.val)=affine t (bit (linear q i.val)) aa x :=
    affine_congr_on t _ _ _ _ (fun k hk=>extendPair_restrict Finset.univ i j x k hk)
  have hB (x:Fin n→F₂) : B (fun k=>x k.val)=affine t (bit (linear q j.val)) bb x :=
    affine_congr_on t _ _ _ _ (fun k hk=>extendPair_restrict Finset.univ i j x k hk)
  have hcross:m i j+m j i=1 := by
    change bit (entry q i.val j.val)+bit (entry q j.val i.val)=1
    rw [←bit_xor]
    change bit (cross q i.val j.val)=1
    rw [hp,bit_true]
  have hphase (x:Fin n→F₂) : phase n q x =
      C (fun k=>x k.val)+x i*x j+A (fun k=>x k.val)*x i+B (fun k=>x k.val)*x j := by
    rw [hC,hA,hB]
    unfold phase
    rw [form_extract_pair Finset.univ i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
    change form t (bit q.1) l m x+(m i j+m j i)*x i*x j+
      x i*affine t (l i+m i i) (fun k=>m i k+m k i) x+
      x j*affine t (l j+m j j) (fun k=>m j k+m k j) x = _
    rw [hcross]
    simp only [aa,bb,l,m,linear,cross,rawLinear,bit_xor]
    ring
  have hres (x:Fin n→F₂) : phase n (pivot q i.val j.val) x=
      C (fun k=>x k.val)+A (fun k=>x k.val)*B (fun k=>x k.val) := by
    rw [hC,hA,hB,phase_pivot q hn i j,form_add_affine_product]
  unfold gauss
  simp_rw [hphase,hres]
  exact pair_elimination i j hij A B C

end PlanarHom.BooleanQuadratic
