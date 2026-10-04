import PlanarHom.DensePolynomialCode
import PlanarHom.IntegerCoordinateBounds
import PlanarHom.CoefficientListHeights

/-! Explicit axis and common-rational-denominator certificates for physical
dense codes. These control trailing zero padding as well as actual coefficients;
primitive FP alone is not used as a bound for polynomial-length iterations. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.DensePolynomial

def BoxBound : (n:ℕ)→ℕ→Code n→Prop
  | 0,_,_ => True
  | n+1,W,a => a.length≤W ∧ ∀b∈a,BoxBound n W b

def CoeffBound : (n:ℕ)→ℕ→ℕ→Code n→Prop
  | 0,D,H,a => ∃z:ℤ,(D:ℚ)*a=z ∧ z.natAbs≤H
  | n+1,D,H,a => ∀b∈a,CoeffBound n D H b

theorem box_zero (n W:ℕ) : BoxBound n W (zero n) := by
  cases n
  · trivial
  · exact ⟨Nat.zero_le _,fun b hb=>False.elim (List.not_mem_nil hb)⟩
theorem coeff_zero (n D H:ℕ) : CoeffBound n D H (zero n) := by
  cases n
  · exact ⟨0,by simp [zero],by simp⟩
  · exact fun b hb=>False.elim (List.not_mem_nil hb)

theorem box_mono (n:ℕ) {W V:ℕ} (h:W≤V) {a:Code n} (ha:BoxBound n W a) : BoxBound n V a := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ha.1.trans h,fun b hb=>ih (ha.2 b hb)⟩

theorem coeff_mono (n D:ℕ) {H B:ℕ} (h:H≤B) {a:Code n} (ha:CoeffBound n D H a) :
    CoeffBound n D B a := by
  induction n with
  | zero => obtain ⟨z,hz,hb⟩:=ha; exact ⟨z,hz,hb.trans h⟩
  | succ n ih => exact fun b hb=>ih (ha b hb)

private theorem lookup_property {A:Type} (P:A→Prop) (z:A) (hz:P z) (xs:List A)
    (h:∀x∈xs,P x) (k:ℕ) : P (xs[k]?.getD z) := by
  cases hh:xs[k]? with
  | none => simpa only [hh,Option.getD_none] using hz
  | some x => simpa only [hh,Option.getD_some] using h x (List.mem_of_getElem? hh)

theorem width_le {A:Type} (xs:List (List A)) (W:ℕ) (h:∀x∈xs,x.length≤W) : width xs≤W := by
  rcases fold_wider_choice xs [] with hz|hm
  · simp only [width,longest,hz,List.length_nil,Nat.zero_le]
  · exact h _ hm

theorem box_sum (n W:ℕ) (xs:List (Code n)) (h:∀x∈xs,BoxBound n W x) :
    BoxBound n W (sum n xs) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    constructor
    · simpa only [sum,List.length_map,List.length_range] using width_le xs W (fun x hx=>(h x hx).1)
    · intro y hy
      obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hy
      apply ih
      intro b hb
      obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hb
      exact lookup_property _ (zero n) (box_zero n W) p (h p hp).2 k

private theorem rational_sum_certificate (D H:ℕ) (xs:List ℚ)
    (h:∀x∈xs,∃z:ℤ,(D:ℚ)*x=z ∧ z.natAbs≤H) :
    ∃z:ℤ,(D:ℚ)*xs.sum=z ∧ z.natAbs≤xs.length*H := by
  let z:Fin xs.length→ℤ:=fun i=>Classical.choose (h (xs.get i) (List.get_mem xs i))
  have hz:∀i,(D:ℚ)*xs.get i=z i ∧ (z i).natAbs≤H:=
    fun i=>Classical.choose_spec (h (xs.get i) (List.get_mem xs i))
  have hx : (∑i:Fin xs.length,xs.get i)=xs.sum := by
    rw [←List.sum_ofFn,List.ofFn_get]
  refine ⟨∑i,z i,?_,?_⟩
  · rw [←hx,Finset.mul_sum,Int.cast_sum]
    exact Finset.sum_congr rfl (fun i _=>(hz i).1)
  · exact (IntegerCoordinateBounds.natAbs_sum_le Finset.univ z).trans
      (by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>(hz i).2))

theorem coeff_sum (n D H:ℕ) (xs:List (Code n)) (h:∀x∈xs,CoeffBound n D H x) :
    CoeffBound n D (xs.length*H) (sum n xs) := by
  induction n with
  | zero => exact rational_sum_certificate D H xs h
  | succ n ih =>
    intro y hy
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hy
    have hh:∀b∈gather (zero n) k xs,CoeffBound n D H b := by
      intro b hb
      obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hb
      exact lookup_property _ (zero n) (coeff_zero n D H) p (h p hp) k
    simpa only [gather,List.length_map] using ih (gather (zero n) k xs) hh

private theorem zipIdx_mem_value {A:Type} {xs:List A} {p:A×ℕ} (h:p∈xs.zipIdx) : p.1∈xs := by
  have hm:p.1∈xs.zipIdx.map Prod.fst:=List.mem_map.mpr ⟨p,h,rfl⟩
  simpa only [List.zipIdx_map_fst] using hm

theorem box_mul (n W V:ℕ) (a b:Code n) (ha:BoxBound n W a) (hb:BoxBound n V b) :
    BoxBound n (W+V+1) (mul n a b) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    constructor
    · change ((List.range (a.length+b.length+1)).map _).length≤_
      simp only [List.length_map,List.length_range]
      have hla:=ha.1
      have hlb:=hb.1
      omega
    · intro c hc
      obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hc
      apply box_sum
      intro term hterm
      obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hterm
      unfold CoefficientConvolutionMachines.term
      dsimp only
      split_ifs
      · exact box_zero _ _
      · apply ih
        · exact ha.2 p.1 (zipIdx_mem_value hp)
        · exact lookup_property _ (zero n) (box_zero n V) b hb.2 _

theorem coeff_mul (n W V D E H J:ℕ) (a b:Code n)
    (hboxa:BoxBound n W a) (hboxb:BoxBound n V b)
    (ha:CoeffBound n D H a) (hb:CoeffBound n E J b) :
    CoeffBound n (D*E) (W^n*H*J) (mul n a b) := by
  induction n with
  | zero =>
    obtain ⟨x,hx,hxb⟩:=ha
    obtain ⟨y,hy,hyb⟩:=hb
    refine ⟨x*y,?_,?_⟩
    · change ((D*E:ℕ):ℚ)*(a*b)=((x*y:ℤ):ℚ)
      rw [Nat.cast_mul,Int.cast_mul,←hx,←hy]
      ring
    · simpa only [pow_zero,one_mul,Int.natAbs_mul] using Nat.mul_le_mul hxb hyb
  | succ n ih =>
    intro c hc
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hc
    let ts:=a.zipIdx.map (fun p=>CoefficientConvolutionMachines.term (zero n)
      (fun _:ℕ=>mul n) ((0,(b,k)),p))
    have ht:∀t∈ts,CoeffBound n (D*E) (W^n*H*J) t := by
      intro t ht
      obtain ⟨p,hp,rfl⟩:=List.mem_map.mp ht
      unfold CoefficientConvolutionMachines.term
      dsimp only
      split_ifs
      · exact coeff_zero _ _ _
      · have hp':p.1∈a:=zipIdx_mem_value hp
        exact ih _ _ (hboxa.2 _ hp')
          (lookup_property _ (zero n) (box_zero n V) b hboxb.2 _)
          (ha _ hp') (lookup_property _ (zero n) (coeff_zero n E J) b hb _)
    have hs:=coeff_sum n (D*E) (W^n*H*J) ts ht
    apply coeff_mono n (D*E) _ hs
    simp only [ts,List.length_map,List.length_zipIdx,pow_succ]
    have h:=Nat.mul_le_mul_right (W^n*H*J) hboxa.1
    nlinarith

end PlanarHom.DensePolynomial
