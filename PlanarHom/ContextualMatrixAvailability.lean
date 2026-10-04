import PlanarHom.AlgebraicLanguageExtensions

/-! Contextual availability retains arbitrary fixed binary and unary companions.
Finite joint availability is proved by genuine appended-language machines and
canonical field conversions, rather than inferred from individual reductions. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases
variable {q bt ut s n : ℕ}

def appendMatrices (L : RealLanguage q bt ut) (N : Fin n → Matrix (Fin q) (Fin q) ℝ)
    (hN : ∀ l i j,IsAlgebraic ℚ (N l i j)) : RealLanguage q (bt+n) ut where
  matrices := appendFamily L.matrices N
  unaries := L.unaries
  weights := L.weights
  matrices_algebraic l := by
    refine Fin.addCases (fun k=>?_) (fun k=>?_) l
    · simpa only [appendFamily,Fin.addCases_left] using L.matrices_algebraic k
    · simpa only [appendFamily,Fin.addCases_right] using hN k
  unaries_algebraic := L.unaries_algebraic
  weights_algebraic := L.weights_algebraic

def ContainsMatrices (L : RealLanguage q bt ut) (F : Fin s → Matrix (Fin q) (Fin q) ℝ) : Prop :=
  ∃ index : Fin s → Fin bt, ∀ l,L.matrices (index l)=F l

theorem containsMatrices_append (L : RealLanguage q bt ut)
    (F : Fin s → Matrix (Fin q) (Fin q) ℝ) (hF : L.ContainsMatrices F)
    (N : Fin n → Matrix (Fin q) (Fin q) ℝ) (hN : ∀ l i j,IsAlgebraic ℚ (N l i j)) :
    (L.appendMatrices N hN).ContainsMatrices F := by
  obtain ⟨index,hi⟩ := hF
  exact ⟨fun l=>Fin.castAdd n (index l),fun l=>by
    simpa only [appendMatrices,appendFamily_old] using hi l⟩

structure ContextuallyAvailable (F : Fin s → Matrix (Fin q) (Fin q) ℝ)
    (N : Matrix (Fin q) (Fin q) ℝ) : Prop where
  algebraic : ∀ i j,IsAlgebraic ℚ (N i j)
  reduction : ∀ {bt ut} (L : RealLanguage q bt ut), (∀ i,L.weights i=1) →
    L.ContainsMatrices F → Nonempty (PromisePolyTimeTuringReduction
      (L.appendBinary N algebraic).problem L.problem)

theorem contextual_generator (F : Fin s → Matrix (Fin q) (Fin q) ℝ)
    (hF : ∀ l i j,IsAlgebraic ℚ (F l i j)) (l : Fin s) : ContextuallyAvailable F (F l) := by
  refine ⟨hF l,?_⟩
  intro bt ut L _ hcontains
  obtain ⟨index,hi⟩ := hcontains
  refine ⟨relabelReduction (L.appendBinary (F l) (hF l)) L (aliasAux (index l)) id ?_ ?_ ?_⟩
  · intro k
    refine Fin.addCases (fun a=>?_) (fun a=>?_) k
    · simp only [appendBinary,appendOne_old,aliasAux_old, implies_true]
    · simpa only [appendBinary,appendOne,aliasAux,Fin.addCases_right] using
        (fun i j=>congrFun (congrFun (hi l).symm i) j)
  · exact fun _ _=>rfl
  · exact fun _=>rfl

/-- Every fixed finite family of contextually available matrices is jointly
available in each context, with every old label and the original oracle kept. -/
theorem contextual_family_reduction (F : Fin s → Matrix (Fin q) (Fin q) ℝ)
    (L : RealLanguage q bt ut) (hunit : ∀ i,L.weights i=1) (hF : L.ContainsMatrices F)
    (N : Fin n → Matrix (Fin q) (Fin q) ℝ) (hN : ∀ l,ContextuallyAvailable F (N l)) :
    Nonempty (PromisePolyTimeTuringReduction
      (L.appendMatrices N (fun l=>(hN l).algebraic)).problem L.problem) := by
  induction n with
  | zero =>
    exact ⟨relabelReduction _ L id id
      (fun l i j=>congrFun (congrFun (congrFun (appendFamily_zero L.matrices N) l) i) j)
      (fun _ _=>rfl) (fun _=>rfl)⟩
  | succ n ih =>
    let V := L.appendMatrices (fun i : Fin n=>N i.castSucc) (fun l=>(hN l.castSucc).algebraic)
    obtain ⟨prev⟩ := ih (fun i=>N i.castSucc) (fun i=>hN i.castSucc)
    obtain ⟨last⟩ := (hN (Fin.last n)).reduction V hunit
      (L.containsMatrices_append F hF _ _)
    have reorder := relabelReduction (L.appendMatrices N (fun l=>(hN l).algebraic))
      (V.appendBinary (N (Fin.last n)) (hN (Fin.last n)).algebraic) id id
      (fun l i j=>congrFun (congrFun (congrFun (appendFamily_succ L.matrices N) l) i) j)
      (fun _ _=>rfl) (fun _=>rfl)
    exact ⟨reorder.trans (last.trans prev)⟩

/-- Close a contextual family under an actual operation on finitely many
available inputs. Auxiliary input labels are added and then eliminated by
the preceding theorem; they do not remain in the supplied source oracle. -/
theorem contextual_operation (F : Fin s → Matrix (Fin q) (Fin q) ℝ)
    (A : Fin n → Matrix (Fin q) (Fin q) ℝ) (hA : ∀ l,ContextuallyAvailable F (A l))
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀ i j,IsAlgebraic ℚ (N i j))
    (operation : ∀ {bt ut} (L : RealLanguage q bt ut), (∀ i,L.weights i=1) →
      ∀ index : Fin n → Fin bt, (∀ l,L.matrices (index l)=A l) →
      Nonempty (PromisePolyTimeTuringReduction (L.appendBinary N hN).problem L.problem)) :
    ContextuallyAvailable F N := by
  refine ⟨hN,?_⟩
  intro bt ut L hunit hF
  let V := L.appendMatrices A (fun l=>(hA l).algebraic)
  obtain ⟨prior⟩ := contextual_family_reduction F L hunit hF A hA
  obtain ⟨op⟩ := operation V hunit (Fin.natAdd bt)
    (fun l=>appendFamily_new L.matrices A l)
  let index : Fin (bt+1) → Fin (bt+n+1) :=
    Fin.addCases (fun l=>Fin.castAdd 1 (Fin.castAdd n l)) (fun _=>Fin.last (bt+n))
  have hinclude := relabelReduction (L.appendBinary N hN) (V.appendBinary N hN) index id
    (by
      intro l
      refine Fin.addCases (fun k=>?_) (fun k=>?_) l
      · simp only [index,Fin.addCases_left,appendBinary,appendOne_old,V,appendMatrices,appendFamily_old]
        exact fun _ _=>True.intro
      · simp only [index,Fin.addCases_right,appendBinary,appendOne,Fin.addCases_right]
        rw [show (Fin.last (bt+n))=Fin.natAdd (bt+n) (0:Fin 1) from Fin.ext rfl]
        simp only [Fin.addCases_right]
        exact fun _ _=>True.intro)
    (fun _ _=>rfl) (fun _=>rfl)
  exact ⟨hinclude.trans (op.trans prior)⟩

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
