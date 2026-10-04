import PlanarHom.PrescribedDomainAliasReductions
import PlanarHom.DomainProductInterpolationReductions

/-! # Appended-constraint coexistence and finite-family joint availability -/
namespace PlanarHom.FiniteLanguageAliases

theorem appendOne_eq_of_ne_aux {α : Type} {n : ℕ} (F : Fin n→α) (x y : α)
    (i : Fin (n+1)) (hi : i.val≠n) : appendOne F x i=appendOne F y i := by
  revert hi
  refine Fin.addCases (fun j _ => ?_) (fun j h => ?_) i
  · rw [appendOne_old,appendOne_old]
  · have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simp at h

/-- Canonical disjoint finite-language union, preserving all original indices. -/
def appendFamily {α : Type} {n r : ℕ} (F : Fin n→α) (G : Fin r→α) : Fin (n+r)→α :=
  fun i => Fin.addCases (m:=n) (n:=r) F G i

@[simp] theorem appendFamily_old {α : Type} {n r : ℕ} (F : Fin n→α) (G : Fin r→α) (i : Fin n) :
    appendFamily F G (Fin.castAdd r i)=F i := Fin.addCases_left i

@[simp] theorem appendFamily_new {α : Type} {n r : ℕ} (F : Fin n→α) (G : Fin r→α) (i : Fin r) :
    appendFamily F G (Fin.natAdd n i)=G i := Fin.addCases_right i

theorem appendFamily_zero {α : Type} {n : ℕ} (F : Fin n→α) (G : Fin 0→α) : appendFamily F G=F := by
  funext i
  change appendFamily F G (Fin.castAdd 0 i)=F i
  exact appendFamily_old F G i

/-- Finite language union in canonical order is successive appending, without
renaming or deleting any old constraint slot. -/
theorem appendFamily_succ {α : Type} {n r : ℕ} (F : Fin n→α) (G : Fin (r+1)→α) :
    appendFamily F G=appendOne (appendFamily F (fun i : Fin r => G i.castSucc)) (G (Fin.last r)) := by
  funext i
  refine Fin.addCases (m:=n) (n:=r+1) (fun j => ?_) (fun j => ?_) i
  · have hj : (Fin.castAdd (r+1) j : Fin (n+(r+1)))=Fin.castAdd 1 (Fin.castAdd r j) := Fin.ext rfl
    rw [appendFamily_old,hj,appendOne_old,appendFamily_old]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · have hj : (Fin.natAdd n (Fin.last r) : Fin (n+(r+1)))=Fin.last (n+r) := Fin.ext rfl
      rw [appendFamily_new,hj,appendOne_aux]
    · have hj : (Fin.natAdd n k.castSucc : Fin (n+(r+1)))=Fin.castAdd 1 (Fin.natAdd n k) := Fin.ext rfl
      rw [appendFamily_new,hj,appendOne_old,appendFamily_new]

end PlanarHom.FiniteLanguageAliases

namespace PlanarHom.Complexity.MixedCode
noncomputable section
open PlanarHom.FiniteLanguageAliases PlanarHom.ProductCompatibility
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {q dimension bt ut d : ℕ}

/-- Append C' while retaining the whole original language including C. The
interpolation replaces only the extra slot; the queried duplicate C slot is
then merged into the existing C label by an actual alias machine. -/
noncomputable def binaryAppendProductReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K)
    (N : Matrix (Fin q) (Fin q) K) (old : Fin bt)
    (hzero : ∀i j,M old i j=0→N i j=0)
    (hproducts : HasProductMaps (fun p : Fin q×Fin q => M old p.1 p.2) (fun p => N p.1 p.2)) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (appendOne M N) U w)
      (evaluationProblem basis M U w) := by
  have rp := binaryProductReduction basis (appendOne M (M old)) (appendOne M N) U w (Fin.last bt)
    (fun l hl => appendOne_eq_of_ne_aux M N (M old) l hl)
    (by simpa only [appendOne_aux] using hzero) (by simpa only [appendOne_aux] using hproducts)
  have ra := binaryRelabelReduction basis (aliasAux old) M U w
  have ra' : PromisePolyTimeTuringReduction (evaluationProblem basis (appendOne M (M old)) U w)
      (evaluationProblem basis M U w) := by simpa only [comp_aliasAux] using ra
  exact rp.trans ra'

noncomputable def unaryAppendProductReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K)
    (N : Fin q→K) (old : Fin ut) (hzero : ∀i,U old i=0→N i=0)
    (hproducts : HasProductMaps (U old) N) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M (appendOne U N) w)
      (evaluationProblem basis M U w) := by
  have rp := unaryProductReduction basis M (appendOne U (U old)) (appendOne U N) w (Fin.last ut)
    (fun l hl => appendOne_eq_of_ne_aux U N (U old) l hl)
    (by simpa only [appendOne_aux] using hzero) (by simpa only [appendOne_aux] using hproducts)
  have ra := unaryRelabelReduction basis (aliasAux old) M U w
  have ra' : PromisePolyTimeTuringReduction (evaluationProblem basis M (appendOne U (U old)) w)
      (evaluationProblem basis M U w) := by simpa only [comp_aliasAux] using ra
  exact rp.trans ra'

/-- Domain-aware appended binary coexistence. The auxiliary constraint may have
only endpoint-domain pairs allowed by its chosen original source label. -/
noncomputable def domainBinaryAppendProductReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K) (D : Fin d→Set (Fin q))
    (B : Fin bt→Fin d→Fin d→Prop) (T : Fin ut→Fin d→Prop)
    (N : Matrix (Fin q) (Fin q) K) (BN : Fin d→Fin d→Prop) (old : Fin bt)
    (htype : ∀x y,BN x y→B old x y)
    (hzero : ∀i j,M old i j=0→N i j=0)
    (hproducts : HasProductMaps (fun p : Fin q×Fin q => M old p.1 p.2) (fun p => N p.1 p.2)) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis (appendOne M N) U w D (appendOne B BN) T)
      (domainEvaluationProblem basis M U w D B T) := by
  have rp := domainBinaryProductReduction basis (appendOne M (M old)) (appendOne M N) U w D (appendOne B BN) T
    (Fin.last bt) (fun l hl => appendOne_eq_of_ne_aux M N (M old) l hl)
    (by simpa only [appendOne_aux] using hzero) (by simpa only [appendOne_aux] using hproducts)
  have hc : ∀i x y,appendOne B BN i x y→B (aliasAux old i) x y := by
    intro i x y
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [appendOne_old,aliasAux_old]; exact id
    · simpa only [appendOne,aliasAux,Fin.addCases_right] using htype x y
  have ra := domainBinaryRelabelReduction basis (aliasAux old) M U w D (appendOne B BN) B T hc
  have ra' : PromisePolyTimeTuringReduction (domainEvaluationProblem basis (appendOne M (M old)) U w D (appendOne B BN) T)
      (domainEvaluationProblem basis M U w D B T) := by simpa only [comp_aliasAux] using ra
  exact rp.trans ra'

/-- Domain-aware unary coexistence, including the exact reserved-offset change
at the final alias and preservation of the original δ throughout. -/
noncomputable def domainUnaryAppendProductReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K) (D : Fin d→Set (Fin q))
    (B : Fin bt→Fin d→Fin d→Prop) (T : Fin ut→Fin d→Prop)
    (N : Fin q→K) (TN : Fin d→Prop) (old : Fin ut) (htype : ∀x,TN x→T old x)
    (hzero : ∀i,U old i=0→N i=0) (hproducts : HasProductMaps (U old) N) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M (appendOne U N) w D B (appendOne T TN))
      (domainEvaluationProblem basis M U w D B T) := by
  have rp := domainUnaryProductReduction basis M (appendOne U (U old)) (appendOne U N) w D B (appendOne T TN)
    (Fin.last ut) (fun l hl => appendOne_eq_of_ne_aux U N (U old) l hl)
    (by simpa only [appendOne_aux] using hzero) (by simpa only [appendOne_aux] using hproducts)
  have hc : ∀i x,appendOne T TN i x→T (aliasAux old i) x := by
    intro i x
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [appendOne_old,aliasAux_old]; exact id
    · simpa only [appendOne,aliasAux,Fin.addCases_right] using htype x
  have ra := domainUnaryRelabelReduction basis (aliasAux old) M U w D B (appendOne T TN) T hc
  have ra' : PromisePolyTimeTuringReduction (domainEvaluationProblem basis M (appendOne U (U old)) w D B (appendOne T TN))
      (domainEvaluationProblem basis M U w D B T) := by simpa only [comp_aliasAux] using ra
  exact rp.trans ra'

/-- Any fixed finite family of new binary constraints is jointly available
from the same original source, with all original constraints coexisting. -/
noncomputable def binaryFiniteProduct_joint {r : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K)
    (N : Fin r→Matrix (Fin q) (Fin q) K) (old : Fin r→Fin bt)
    (hzero : ∀j i k,M (old j) i k=0→N j i k=0)
    (hproducts : ∀j,HasProductMaps (fun p : Fin q×Fin q => M (old j) p.1 p.2) (fun p => N j p.1 p.2))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (evaluationProblem basis M U w) base) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (appendFamily M N) U w) base := by
  induction r with
  | zero => simpa only [appendFamily_zero] using available
  | succ r ih =>
    have prev := ih (fun i => N i.castSucc) (fun i => old i.castSucc)
      (fun j => hzero j.castSucc) (fun j => hproducts j.castSucc)
    have last := binaryAppendProductReduction basis (appendFamily M (fun i : Fin r => N i.castSucc)) U w
      (N (Fin.last r)) (Fin.castAdd r (old (Fin.last r)))
      (by simpa only [appendFamily_old] using hzero (Fin.last r))
      (by simpa only [appendFamily_old] using hproducts (Fin.last r))
    simpa only [←appendFamily_succ] using last.trans prev

noncomputable def unaryFiniteProduct_joint {r : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K)
    (N : Fin r→Fin q→K) (old : Fin r→Fin ut) (hzero : ∀j i,U (old j) i=0→N j i=0)
    (hproducts : ∀j,HasProductMaps (U (old j)) (N j))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (evaluationProblem basis M U w) base) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M (appendFamily U N) w) base := by
  induction r with
  | zero => simpa only [appendFamily_zero] using available
  | succ r ih =>
    have prev := ih (fun i => N i.castSucc) (fun i => old i.castSucc)
      (fun j => hzero j.castSucc) (fun j => hproducts j.castSucc)
    have last := unaryAppendProductReduction basis M (appendFamily U (fun i : Fin r => N i.castSucc)) w
      (N (Fin.last r)) (Fin.castAdd r (old (Fin.last r)))
      (by simpa only [appendFamily_old] using hzero (Fin.last r))
      (by simpa only [appendFamily_old] using hproducts (Fin.last r))
    simpa only [←appendFamily_succ] using last.trans prev

/-- Finite binary families retain the original prescribed domains and every
companion. Each auxiliary label is merged only after its actual interpolation. -/
noncomputable def domainBinaryFiniteProduct_joint {r : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K) (D : Fin d→Set (Fin q))
    (B : Fin bt→Fin d→Fin d→Prop) (T : Fin ut→Fin d→Prop)
    (N : Fin r→Matrix (Fin q) (Fin q) K) (BN : Fin r→Fin d→Fin d→Prop) (old : Fin r→Fin bt)
    (htype : ∀j x y,BN j x y→B (old j) x y)
    (hzero : ∀j i k,M (old j) i k=0→N j i k=0)
    (hproducts : ∀j,HasProductMaps (fun p : Fin q×Fin q => M (old j) p.1 p.2) (fun p => N j p.1 p.2))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U w D B T) base) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis (appendFamily M N) U w D (appendFamily B BN) T) base := by
  induction r with
  | zero => simpa only [appendFamily_zero] using available
  | succ r ih =>
    have prev := ih (fun i => N i.castSucc) (fun i => BN i.castSucc) (fun i => old i.castSucc)
      (fun j => htype j.castSucc) (fun j => hzero j.castSucc) (fun j => hproducts j.castSucc)
    have last := domainBinaryAppendProductReduction basis (appendFamily M (fun i : Fin r => N i.castSucc)) U w D
      (appendFamily B (fun i : Fin r => BN i.castSucc)) T (N (Fin.last r)) (BN (Fin.last r))
      (Fin.castAdd r (old (Fin.last r)))
      (by simpa only [appendFamily_old] using htype (Fin.last r))
      (by simpa only [appendFamily_old] using hzero (Fin.last r))
      (by simpa only [appendFamily_old] using hproducts (Fin.last r))
    simpa only [←appendFamily_succ] using last.trans prev

/-- Finite unary families preserve each original domain index while adjusting
reserved offsets at every appended-label alias; no new pinning is introduced. -/
noncomputable def domainUnaryFiniteProduct_joint {r : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K) (D : Fin d→Set (Fin q))
    (B : Fin bt→Fin d→Fin d→Prop) (T : Fin ut→Fin d→Prop)
    (N : Fin r→Fin q→K) (TN : Fin r→Fin d→Prop) (old : Fin r→Fin ut)
    (htype : ∀j x,TN j x→T (old j) x) (hzero : ∀j i,U (old j) i=0→N j i=0)
    (hproducts : ∀j,HasProductMaps (U (old j)) (N j))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U w D B T) base) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M (appendFamily U N) w D B (appendFamily T TN)) base := by
  induction r with
  | zero => simpa only [appendFamily_zero] using available
  | succ r ih =>
    have prev := ih (fun i => N i.castSucc) (fun i => TN i.castSucc) (fun i => old i.castSucc)
      (fun j => htype j.castSucc) (fun j => hzero j.castSucc) (fun j => hproducts j.castSucc)
    have last := domainUnaryAppendProductReduction basis M (appendFamily U (fun i : Fin r => N i.castSucc)) w D B
      (appendFamily T (fun i : Fin r => TN i.castSucc)) (N (Fin.last r)) (TN (Fin.last r))
      (Fin.castAdd r (old (Fin.last r)))
      (by simpa only [appendFamily_old] using htype (Fin.last r))
      (by simpa only [appendFamily_old] using hzero (Fin.last r))
      (by simpa only [appendFamily_old] using hproducts (Fin.last r))
    simpa only [←appendFamily_succ] using last.trans prev

/-- Simultaneous binary and unary finite families coexist with the entire
original language, using its one original supplied availability witness. -/
noncomputable def mixedFiniteProduct_joint {r s : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K)
    (N : Fin r→Matrix (Fin q) (Fin q) K) (V : Fin s→Fin q→K)
    (oldM : Fin r→Fin bt) (oldU : Fin s→Fin ut)
    (hzeroM : ∀j i k,M (oldM j) i k=0→N j i k=0)
    (hproductsM : ∀j,HasProductMaps (fun p : Fin q×Fin q => M (oldM j) p.1 p.2) (fun p => N j p.1 p.2))
    (hzeroU : ∀j i,U (oldU j) i=0→V j i=0) (hproductsU : ∀j,HasProductMaps (U (oldU j)) (V j))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (evaluationProblem basis M U w) base) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (appendFamily M N) (appendFamily U V) w) base :=
  unaryFiniteProduct_joint basis (appendFamily M N) U w V oldU hzeroU hproductsU base
    (binaryFiniteProduct_joint basis M U w N oldM hzeroM hproductsM base available)

/-- The same simultaneous finite-family statement on the exact intrinsic-domain
model, preserving all original allowed domains and every companion constraint. -/
noncomputable def domainMixedFiniteProduct_joint {r s : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K) (D : Fin d→Set (Fin q))
    (B : Fin bt→Fin d→Fin d→Prop) (T : Fin ut→Fin d→Prop)
    (N : Fin r→Matrix (Fin q) (Fin q) K) (V : Fin s→Fin q→K)
    (BN : Fin r→Fin d→Fin d→Prop) (TV : Fin s→Fin d→Prop)
    (oldM : Fin r→Fin bt) (oldU : Fin s→Fin ut)
    (htypeM : ∀j x y,BN j x y→B (oldM j) x y) (htypeU : ∀j x,TV j x→T (oldU j) x)
    (hzeroM : ∀j i k,M (oldM j) i k=0→N j i k=0)
    (hproductsM : ∀j,HasProductMaps (fun p : Fin q×Fin q => M (oldM j) p.1 p.2) (fun p => N j p.1 p.2))
    (hzeroU : ∀j i,U (oldU j) i=0→V j i=0) (hproductsU : ∀j,HasProductMaps (U (oldU j)) (V j))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U w D B T) base) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendFamily M N) (appendFamily U V) w D (appendFamily B BN) (appendFamily T TV)) base :=
  domainUnaryFiniteProduct_joint basis (appendFamily M N) U w D (appendFamily B BN) T V TV oldU htypeU hzeroU hproductsU base
    (domainBinaryFiniteProduct_joint basis M U w D B T N BN oldM htypeM hzeroM hproductsM base available)

end
end PlanarHom.Complexity.MixedCode
