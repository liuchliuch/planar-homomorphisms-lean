import PlanarHom.RectangularMixedPhysicalForms

/-! NEW boundary checks for genuine graph geometry and arbitrary signed forms. -/
noncomputable section
namespace PlanarHom.RectangularMixedGadgets.Regressions
open PlanarHom.RectangularMixedGadgets

example : TwoTerminal.PlanarEdgeGadget doubleDiamond := doubleDiamond_planarEdgeGadget
example : doubleDiamond.src 0=Sum.inl false ∧ doubleDiamond.dst 7=Sum.inl true := ⟨rfl,rfl⟩
example : (fun k : Fin 5=>vertexSide (.inr k))=![0,0,1,0,0] := by
  funext k; fin_cases k <;> rfl
example : label 0=0 ∧ label 1=1 ∧ label 5=0 ∧ label 6=1 := ⟨rfl,rfl,rfl,rfl⟩

example (B : Matrix (Fin 2) (Fin 3) ℝ) (K : Matrix (Fin 2) (Fin 2) ℝ)
    (hK : K.transpose=K) :
    TwoTerminal.coloredSignature doubleDiamond (edgeMatrices (onX K) (cross B)) (fun _=>1)=
      onX (entrySquare (K*B)*(entrySquare (K*B)).transpose) :=
  doubleDiamond_physical_gram B K hK

example (B : Matrix (Fin 0) (Fin 3) ℝ) (K : Matrix (Fin 0) (Fin 0) ℝ)
    (hK : K.transpose=K) :
    TwoTerminal.coloredSignature doubleDiamond (edgeMatrices (onX K) (cross B)) (fun _=>1)=
      onX (entrySquare (K*B)*(entrySquare (K*B)).transpose) :=
  doubleDiamond_physical_gram B K hK

example (B : Matrix (Fin 2) (Fin 0) ℝ) (K : Matrix (Fin 2) (Fin 2) ℝ)
    (hK : K.transpose=K) :
    TwoTerminal.coloredSignature doubleDiamond (edgeMatrices (onX K) (cross B)) (fun _=>1)=
      onX (entrySquare (K*B)*(entrySquare (K*B)).transpose) :=
  doubleDiamond_physical_gram B K hK

example (K B : Matrix (Fin 0) (Fin 0) ℚ) :
    TwoTerminal.coloredSignature doubleDiamond (edgeMatrices K B) (fun _=>1)=
      entrySquare (K*B)*entrySquare (B*K) := doubleDiamond_value K B

example (K B : Matrix (Fin 3) (Fin 3) ℤ) (a : Fin 3) :
    TwoTerminal.coloredSignature doubleDiamond (edgeMatrices K B) (fun _=>1) a a =
      (entrySquare (K*B)*entrySquare (B*K)) a a := by
  rw [doubleDiamond_value]

end PlanarHom.RectangularMixedGadgets.Regressions
