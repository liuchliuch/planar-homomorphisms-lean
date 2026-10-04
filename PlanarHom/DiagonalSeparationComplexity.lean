import PlanarHom.PositiveDiagonalRankObstruction
import PlanarHom.PositiveRankOneAmplitudes
import PlanarHom.MainDichotomyFinalAssembly

/-! NEW original-field diagonal-separation complexity assembly. Part (i)
uses literal matrix rank; the explicit basic-block form here is an internal
bridge for the actual support-component rank statement of part (ii). -/
noncomputable section
open Classical
namespace PlanarHom.GadgetDiagonalSeparation
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage Complexity Structures
variable {q:ℕ}

 theorem rank_one_inFP (L:RealLanguage q 1 0)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i) (hp:∀i j,0<L.matrices 0 i j)
    (hr:(L.matrices 0).rank=1) : L.problem.InFP := by
  have hw:=Matrix.rank_le_card_width (L.matrices 0)
  simp only [Fintype.card_fin,hr] at hw
  let r:Fin q:=⟨0,by omega⟩
  obtain ⟨a,ha,hm⟩:=positive_amplitudes_of_rank_le_one (L.matrices 0) r hs hp (by omega)
  exact L.rankOne_inFP a hm

 theorem positive_distinct_diagonals_hard_of_potts (hPotts:PositivePottsFoundation) (L:RealLanguage q 1 0)
    (hunit:∀i,L.weights i=1) (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hp:∀i j,0<L.matrices 0 i j) (hd:Function.Injective (fun i=>L.matrices 0 i i))
    (hr:1<(L.matrices 0).rank) : PromisedSharpPHard L.problem := by
  have hw:=Matrix.rank_le_card_width (L.matrices 0)
  simp only [Fintype.card_fin] at hw
  letI : Nonempty (Fin q):=⟨⟨0,by omega⟩⟩
  apply (L.theorem11_of_potts hPotts hunit hs (fun i j=>(hp i j).le)).2
  intro hclass
  have hh:=nonnegativeClass_rank_le_one (L.matrices 0) hp hd hclass
  omega

 theorem proposition25i_of_potts (hPotts:PositivePottsFoundation) (L:RealLanguage q 1 0)
    (hunit:∀i,L.weights i=1) (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hp:∀i j,0<L.matrices 0 i j) (hd:Function.Injective (fun i=>L.matrices 0 i i)) :
    ((L.matrices 0).rank=1→L.problem.InFP) ∧
      (1<(L.matrices 0).rank→PromisedSharpPHard L.problem) :=
  ⟨rank_one_inFP L hs hp,positive_distinct_diagonals_hard_of_potts hPotts L hunit hs hp hd⟩

 theorem basicClass_inFP (L:RealLanguage q 1 0) (hunit:∀i,L.weights i=1)
    (h:BasicClass (L.matrices 0)) : L.problem.InFP :=
  L.nonnegative_class_inFP hunit h.nonnegativeClass

 theorem separating_basic_dichotomy_of_potts (hPotts:PositivePottsFoundation) (L:RealLanguage q 1 0)
    (hunit:∀i,L.weights i=1) (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn:∀i j,0≤L.matrices 0 i j) (hsep:Separates (L.matrices 0)) :
    (BasicClass (L.matrices 0)→L.problem.InFP) ∧
      (¬BasicClass (L.matrices 0)→PromisedSharpPHard L.problem) := by
  refine ⟨basicClass_inFP L hunit,?_⟩
  intro hbad
  apply (L.theorem11_of_potts hPotts hunit hs hnn).2
  intro hclass
  exact hbad (basicClass_of_separates hsep hclass)

end PlanarHom.GadgetDiagonalSeparation
