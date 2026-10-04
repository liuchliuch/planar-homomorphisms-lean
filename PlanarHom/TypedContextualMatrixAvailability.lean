import PlanarHom.TypedRealLanguagePresentation
import PlanarHom.ContextualMatrixAvailability

/-! Typed contextual availability quantifies over arbitrary retained companions.
Both the literal matrix and its endpoint policy are preserved in every context.
Finite joint availability is constructed by actual appended-language programs. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity FiniteLanguageAliases
variable {q dt s n bt ut : ℕ}

def ContainsTypedMatrices (L : RealLanguage q bt ut)
    (B : Fin bt→Fin dt→Fin dt→Prop) (F : Fin s→Matrix (Fin q) (Fin q) ℝ)
    (FB : Fin s→Fin dt→Fin dt→Prop) : Prop :=
  ∃ index : Fin s→Fin bt,∀l,L.matrices (index l)=F l ∧ B (index l)=FB l

structure TypedContextuallyAvailable (D : Fin dt→Set (Fin q))
    (F : Fin s→Matrix (Fin q) (Fin q) ℝ) (FB : Fin s→Fin dt→Fin dt→Prop)
    (N : Matrix (Fin q) (Fin q) ℝ) (NB : Fin dt→Fin dt→Prop) : Prop where
  algebraic : ∀i j,IsAlgebraic ℚ (N i j)
  reduction : ∀ {bt ut} (L : RealLanguage q bt ut)
    (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop),
    (∀i,L.weights i=1) → L.ContainsTypedMatrices B F FB →
    Nonempty (PromisePolyTimeTuringReduction
      ((L.appendBinary N algebraic).typedProblem D (appendOne B NB) T)
      (L.typedProblem D B T))

theorem containsTypedMatrices_append (L : RealLanguage q bt ut)
    (B : Fin bt→Fin dt→Fin dt→Prop) (F : Fin s→Matrix (Fin q) (Fin q) ℝ)
    (FB : Fin s→Fin dt→Fin dt→Prop) (hF : L.ContainsTypedMatrices B F FB)
    (N : Fin n→Matrix (Fin q) (Fin q) ℝ) (hN : ∀l i j,IsAlgebraic ℚ (N l i j))
    (NB : Fin n→Fin dt→Fin dt→Prop) :
    (L.appendMatrices N hN).ContainsTypedMatrices (appendFamily B NB) F FB := by
  obtain ⟨index,hi⟩ := hF
  refine ⟨fun l=>Fin.castAdd n (index l),?_⟩
  intro l
  simpa only [appendMatrices,appendFamily_old] using hi l

theorem typed_contextual_generator (D : Fin dt→Set (Fin q))
    (F : Fin s→Matrix (Fin q) (Fin q) ℝ) (FB : Fin s→Fin dt→Fin dt→Prop)
    (hF : ∀l i j,IsAlgebraic ℚ (F l i j)) (l : Fin s) :
    TypedContextuallyAvailable D F FB (F l) (FB l) := by
  refine ⟨hF l,?_⟩
  intro bt ut L B T _ hcontains
  obtain ⟨index,hi⟩ := hcontains
  refine ⟨typedRelabelReduction (L.appendBinary (F l) (hF l)) L D
    (appendOne B (FB l)) B T T (aliasAux (index l)) id ?_ (by intros; assumption) ?_
    (fun _ _=>rfl) (fun _=>rfl)⟩
  · intro k
    refine Fin.addCases (fun a=>?_) (fun a=>?_) k
    · intro x y h
      simpa only [appendOne_old,aliasAux_old] using h
    · intro x y h
      simpa only [appendOne,aliasAux,Fin.addCases_right,(hi l).2] using h
  · intro k
    refine Fin.addCases (fun a=>?_) (fun a=>?_) k
    · simp only [appendBinary,appendOne_old,aliasAux_old,implies_true]
    · simpa only [appendBinary,appendOne,aliasAux,Fin.addCases_right] using
        (fun i j=>congrFun (congrFun (hi l).1.symm i) j)

theorem typed_contextual_family_reduction (D : Fin dt→Set (Fin q))
    (F : Fin s→Matrix (Fin q) (Fin q) ℝ) (FB : Fin s→Fin dt→Fin dt→Prop)
    (L : RealLanguage q bt ut) (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (hunit : ∀i,L.weights i=1) (hF : L.ContainsTypedMatrices B F FB)
    (N : Fin n→Matrix (Fin q) (Fin q) ℝ) (NB : Fin n→Fin dt→Fin dt→Prop)
    (hN : ∀l,TypedContextuallyAvailable D F FB (N l) (NB l)) :
    Nonempty (PromisePolyTimeTuringReduction
      ((L.appendMatrices N (fun l=>(hN l).algebraic)).typedProblem D (appendFamily B NB) T)
      (L.typedProblem D B T)) := by
  induction n with
  | zero =>
    refine ⟨typedRelabelReduction _ L D (appendFamily B NB) B T T id id ?_ (by intros; assumption)
      ?_ (fun _ _=>rfl) (fun _=>rfl)⟩
    · intro l x y h
      simpa only [appendFamily_zero,id_eq] using h
    · intro l i j
      exact congrFun (congrFun (congrFun (appendFamily_zero L.matrices N) l) i) j
  | succ n ih =>
    let V := L.appendMatrices (fun i:Fin n=>N i.castSucc) (fun l=>(hN l.castSucc).algebraic)
    let BV := appendFamily B (fun i:Fin n=>NB i.castSucc)
    obtain ⟨prev⟩ := ih (fun i:Fin n=>N i.castSucc) (fun i:Fin n=>NB i.castSucc) (fun i=>hN i.castSucc)
    obtain ⟨last⟩ := (hN (Fin.last n)).reduction V BV T hunit
      (L.containsTypedMatrices_append B F FB hF _ _ _)
    have reorder := typedRelabelReduction
      (L.appendMatrices N (fun l=>(hN l).algebraic))
      (V.appendBinary (N (Fin.last n)) (hN (Fin.last n)).algebraic) D
      (appendFamily B NB) (appendOne BV (NB (Fin.last n))) T T id id
      (fun l x y h=>by simpa only [id_eq,appendFamily_succ,BV] using h)
      (by intros; assumption)
      (fun l i j=>congrFun (congrFun (congrFun (appendFamily_succ L.matrices N) l) i) j)
      (fun _ _=>rfl) (fun _=>rfl)
    exact ⟨reorder.trans (last.trans prev)⟩

theorem typed_contextual_operation (D : Fin dt→Set (Fin q))
    (F : Fin s→Matrix (Fin q) (Fin q) ℝ) (FB : Fin s→Fin dt→Fin dt→Prop)
    (A : Fin n→Matrix (Fin q) (Fin q) ℝ) (AB : Fin n→Fin dt→Fin dt→Prop)
    (hA : ∀l,TypedContextuallyAvailable D F FB (A l) (AB l))
    (N : Matrix (Fin q) (Fin q) ℝ) (NB : Fin dt→Fin dt→Prop) (hN : ∀i j,IsAlgebraic ℚ (N i j))
    (operation : ∀ {bt ut} (L : RealLanguage q bt ut)
      (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop),
      (∀i,L.weights i=1) → ∀ index : Fin n→Fin bt,
      (∀l,L.matrices (index l)=A l ∧ B (index l)=AB l) →
      Nonempty (PromisePolyTimeTuringReduction
        ((L.appendBinary N hN).typedProblem D (appendOne B NB) T) (L.typedProblem D B T))) :
    TypedContextuallyAvailable D F FB N NB := by
  refine ⟨hN,?_⟩
  intro bt ut L B T hunit hF
  let V := L.appendMatrices A (fun l=>(hA l).algebraic)
  let BV := appendFamily B AB
  obtain ⟨prior⟩ := typed_contextual_family_reduction D F FB L B T hunit hF A AB hA
  obtain ⟨op⟩ := operation V BV T hunit (Fin.natAdd bt)
    (fun l=>⟨appendFamily_new L.matrices A l,appendFamily_new B AB l⟩)
  let index : Fin (bt+1)→Fin (bt+n+1) :=
    Fin.addCases (fun l=>Fin.castAdd 1 (Fin.castAdd n l)) (fun _=>Fin.last (bt+n))
  have embed :=  typedRelabelReduction (L.appendBinary N hN) (V.appendBinary N hN) D
    (appendOne B NB) (appendOne BV NB) T T index id
    (by
      intro l
      refine Fin.addCases (fun k=>?_) (fun k=>?_) l
      · intro x y h
        simpa only [index,Fin.addCases_left,appendOne_old,BV,appendFamily_old] using h
      · intro x y h
        simp only [appendOne,Fin.addCases_right] at h
        simp only [index,Fin.addCases_right,appendOne_aux]
        exact h)
    (by intros; assumption)
    (by
      intro l
      refine Fin.addCases (fun k=>?_) (fun k=>?_) l
      · simp only [index,Fin.addCases_left,appendBinary,appendOne_old,V,appendMatrices,appendFamily_old]
        exact fun _ _=>True.intro
      · intro i j
        have hleft : appendOne L.matrices N (Fin.natAdd bt k)=N := by
          simp only [appendOne,Fin.addCases_right]
        simp only [appendBinary,hleft,index,Fin.addCases_right,appendOne_aux])
    (fun _ _=>rfl) (fun _=>rfl)
  exact ⟨embed.trans (op.trans prior)⟩

theorem typed_contextual_of_generators (D : Fin dt→Set (Fin q))
    {t : ℕ} (F : Fin s→Matrix (Fin q) (Fin q) ℝ) (FB : Fin s→Fin dt→Fin dt→Prop)
    (G : Fin t→Matrix (Fin q) (Fin q) ℝ) (GB : Fin t→Fin dt→Fin dt→Prop)
    (hF : ∀l,TypedContextuallyAvailable D G GB (F l) (FB l))
    (N : Matrix (Fin q) (Fin q) ℝ) (NB : Fin dt→Fin dt→Prop)
    (hN : TypedContextuallyAvailable D F FB N NB) : TypedContextuallyAvailable D G GB N NB :=
  typed_contextual_operation D G GB F FB hF N NB hN.algebraic
    (fun L B T hunit index hindex=>hN.reduction L B T hunit ⟨index,hindex⟩)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
