import PlanarHom.TypedMixedPhysicalAvailabilityValues

/-! The original cross generator alone supplies its X-side Gram by an actual
two-edge path with one prescribed Y-private vertex. -/
noncomputable section
open Classical
open scoped BigOperators
open unitInterval
namespace PlanarHom.TypedBipartiteContext
open TypedGadgetAppend PrescribedDomains TypedBipartiteSpectral RectangularMixedGadgets
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage

private def gramHalf : I := ⟨1/2,by norm_num⟩
private def gramPoint : Bool⊕PUnit.{1}→I×I
  | .inl false => (0,0)
  | .inl true => (1,0)
  | .inr _ => (gramHalf,0)
private def gramBlend (a b t : I) : I :=
  ⟨(1-(t:ℝ))*(a:ℝ)+(t:ℝ)*(b:ℝ),by
    refine ⟨add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
      (mul_nonneg t.property.1 b.property.1),?_⟩
    have h₁ := mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr t.property.2)
    have h₂ := mul_le_mul_of_nonneg_left b.property.2 t.property.1
    nlinarith⟩
private def gramCurve (e : Bool) : C(I,I×I) where
  toFun t := (gramBlend (gramPoint (TwoTerminal.twoEdgePath.src e)).1
    (gramPoint (TwoTerminal.twoEdgePath.dst e)).1 t,0)
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      change Continuous (fun t:I=>(1-(t:ℝ))*_+(t:ℝ)*_)
      fun_prop
    · fun_prop
private def gramStrip : TwoTerminal.StripDrawing TwoTerminal.twoEdgePath where
  point := gramPoint
  point_injective := by
    rintro (a|a) (b|b) h <;> cases a <;> cases b <;>
      norm_num [gramPoint,gramHalf,Prod.ext_iff,Subtype.ext_iff] at h
    all_goals rfl
  left := rfl
  right := rfl
  internal_inside := by intro b; cases b; norm_num [gramPoint,gramHalf,MultiGraph.Inside]
  curve := gramCurve
  curve_zero := by intro e; cases e <;> ext <;> simp [gramCurve,gramBlend,gramPoint,TwoTerminal.twoEdgePath]
  curve_one := by intro e; cases e <;> ext <;> simp [gramCurve,gramBlend,gramPoint,TwoTerminal.twoEdgePath]
  curve_inside := by
    intro e t ht
    rcases ht with ⟨ht₀,ht₁⟩
    have htpos : (0:I)<t := ht₀
    have htlt : t<(1:I) := ht₁
    cases e <;> norm_num [gramCurve,gramBlend,gramPoint,TwoTerminal.twoEdgePath,
      gramHalf,MultiGraph.Inside] <;> constructor <;> first | assumption | linarith
  interior_injective := by
    intro e f s t hs ht h
    have hx := congrArg (fun p:I×I=>(p.1:ℝ)) h
    rcases hs with ⟨hs₀,hs₁⟩
    rcases ht with ⟨ht₀,ht₁⟩
    cases e <;> cases f <;>
      norm_num [gramCurve,gramBlend,gramPoint,TwoTerminal.twoEdgePath,gramHalf] at hx ⊢
    all_goals first | (apply Subtype.ext; linarith) | linarith
  interior_avoids := by
    intro e t ht v h
    have hx := congrArg (fun p:I×I=>(p.1:ℝ)) h
    rcases ht with ⟨ht₀,ht₁⟩
    have hn0 : t≠(0:I) := ne_of_gt (show (0:I)<t from ht₀)
    have hn1 : t≠(1:I) := ne_of_lt (show t<(1:I) from ht₁)
    cases e <;> rcases v with (b|b) <;> cases b <;>
      norm_num [gramCurve,gramBlend,gramPoint,TwoTerminal.twoEdgePath,gramHalf] at hx <;>
      first | exact hn0 hx | exact hn1 hx | linarith

/-- The serialized one-private-vertex two-edge path. -/
def crossGramPath : TwoTerminal (Fin 1) (Fin 2) :=
  TwoTerminal.twoEdgePath.reindexInternal (Equiv.ofUnique PUnit (Fin 1)) finTwoEquiv.symm

theorem crossGramPath_planar : TwoTerminal.PlanarEdgeGadget crossGramPath :=
  TwoTerminal.reindexInternal_planar _ _ _ gramStrip.planarEdgeGadget

theorem crossGramPath_edges : ∀a b : Fin 2,sameX a b→∀k,
    crossPolicy (TwoTerminal.extend a b (fun _:Fin 1=>1) (crossGramPath.src k))
      (TwoTerminal.extend a b (fun _:Fin 1=>1) (crossGramPath.dst k)) := by
  intro a b hab k
  obtain ⟨rfl,rfl⟩ := hab
  fin_cases k <;> simp [crossGramPath,TwoTerminal.reindexInternal,MultiGraph.reindex,
    TwoTerminal.twoEdgePath,TwoTerminal.extend,crossPolicy,finTwoEquiv]

variable {x y s : ℕ} {R : Type} [Field R]

theorem crossGram_expanded (B : Matrix (Fin x) (Fin y) R) (a b : Fin (x+y)) :
    coloredDomainInteraction crossGramPath (fun _:Fin 2=>(0:Fin 1))
      (fun _:Fin 1=>(1:Fin 2)) (fun _=>crossFin B) (domains x y) a b=
      ∑c:Fin (x+y),indicator (domains x y 1) c * (crossFin B a c*crossFin B c b) := by
  unfold coloredDomainInteraction
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin (x+y)))
  intro η
  simp [crossGramPath,TwoTerminal.reindexInternal,MultiGraph.reindex,
    TwoTerminal.twoEdgePath,TwoTerminal.extend,Fin.prod_univ_succ,
    Equiv.funUnique,Equiv.piUnique,finTwoEquiv,Equiv.ofUnique]

private theorem gram_indicator_left (c : Fin x) :
    indicator (R:=R) (domains x y 1) (finSumFinEquiv (.inl c))=0 := by
  apply if_neg
  rintro ⟨d,hd⟩
  have h := congrArg Fin.val hd
  change x+d.val=c.val at h
  omega

private theorem gram_indicator_right (c : Fin y) :
    indicator (R:=R) (domains x y 1) (finSumFinEquiv (.inr c))=1 := by
  exact if_pos ⟨c,rfl⟩

/-- One intrinsic Y sum gives precisely the X-side Gram, zero elsewhere. -/
theorem crossGram_physical_value (B : Matrix (Fin x) (Fin y) R) :
    coloredDomainInteraction crossGramPath (fun _:Fin 2=>(0:Fin 1))
      (fun _:Fin 1=>(1:Fin 2)) (fun _=>crossFin B) (domains x y)=
      zeroExtendFin (y:=y) (B*B.transpose) := by
  funext a b
  rw [crossGram_expanded]
  rw [← (finSumFinEquiv : Fin x⊕Fin y≃Fin (x+y)).sum_comp
    (fun c=>indicator (R:=R) (domains x y 1) c*(crossFin B a c*crossFin B c b))]
  rw [Fintype.sum_sum_type]
  simp only [gram_indicator_left,gram_indicator_right,zero_mul,one_mul,
    Finset.sum_const_zero,zero_add]
  obtain ⟨a,rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b,rfl⟩ := finSumFinEquiv.surjective b
  rcases a with a|a <;> rcases b with b|b <;>
    simp [crossFin,Matrix.reindex_apply,cross,zeroExtendFin,zeroExtend,
      Matrix.fromBlocks,Matrix.mul_apply,Matrix.transpose_apply]

/-- An available original cross interaction supplies the Gram in the same
retained X family without needing any Y-side identity matrix. -/
theorem crossGram_mem_xFamily
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (B : Matrix (Fin x) (Fin y) ℝ)
    (hB : TypedContextuallyAvailable (domains x y) F FB (crossFin B) crossPolicy) :
    B*B.transpose∈xFamily F FB := by
  have h := typed_contextual_colored_gadget (domains x y) F FB
    (fun _:Fin 1=>crossFin B) (fun _:Fin 1=>crossPolicy) (fun _=>hB)
    crossGramPath (fun _=>0) (fun _=>1) crossGramPath_planar sameX 0 crossGramPath_edges
  rw [crossGram_physical_value] at h
  refine ⟨?_,h⟩
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_conjTranspose_self B

/-- Source-generator version of the physical two-edge X Gram. -/
theorem crossGram_from_generator_mem_xFamily
    (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ) (FB : Fin s→Fin 2→Fin 2→Prop)
    (hF : ∀l i j,IsAlgebraic ℚ (F l i j)) (old : Fin s)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : F old=crossFin B) (hpolicy : FB old=crossPolicy) :
    B*B.transpose∈xFamily F FB := by
  have hg := typed_contextual_generator (domains x y) F FB hF old
  rw [hB,hpolicy] at hg
  exact crossGram_mem_xFamily F FB B hg

end PlanarHom.TypedBipartiteContext
