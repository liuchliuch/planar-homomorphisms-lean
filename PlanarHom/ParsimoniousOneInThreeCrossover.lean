import PlanarHom.ParsimoniousNorOneInThree

/-!
# Exact one-in-three crossover multiplicity

Four NOR/EQV gadgets share their equivalence output around the four terminal
corners, as in Barbanchon (2004), Appendix C. This file verifies the complete
Boolean boundary relation and unique extension. A plane drawing and the global
crossing-replacement algorithm are separate obligations, not assumed here.
-/
noncomputable section
open Classical
namespace PlanarHom.ParsimoniousNorOneInThree

def auxiliaryExtension (x y : Bool) : Fin 3 → Bool := ![!(x||y),!x&&y,x&&!y]

theorem gate_shared_equivalence (x y e : Bool) (a : Fin 3 → Bool) :
    Gate x y (a 0) e (a 1) (a 2) ↔ e=decide (x=y) ∧ a=auxiliaryExtension x y := by
  rw [gate_iff]
  constructor
  · rintro ⟨hn,he,hi,hj⟩
    refine ⟨he,?_⟩
    funext k
    fin_cases k
    · exact hn
    · exact hi
    · exact hj
  · rintro ⟨rfl,rfl⟩
    exact ⟨rfl,rfl,rfl,rfl⟩

/-- The four adjacent corner pairs share one central EQV variable. -/
def Crossover (x y x' y' e : Bool) (a : Fin 4 → Fin 3 → Bool) : Prop :=
  Gate x y (a 0 0) e (a 0 1) (a 0 2) ∧
  Gate y x' (a 1 0) e (a 1 1) (a 1 2) ∧
  Gate x' y' (a 2 0) e (a 2 1) (a 2 2) ∧
  Gate y' x (a 3 0) e (a 3 1) (a 3 2)

def crossoverAuxiliary (x y : Bool) : Fin 4 → Fin 3 → Bool :=
  ![auxiliaryExtension x y,auxiliaryExtension y x,auxiliaryExtension x y,auxiliaryExtension y x]

/-- The local relation transmits both input bits independently and has exactly
one central and auxiliary assignment for each transmitted boundary. -/
theorem crossover_iff (x y x' y' e : Bool) (a : Fin 4 → Fin 3 → Bool) :
    Crossover x y x' y' e a ↔
      x'=x ∧ y'=y ∧ e=decide (x=y) ∧ a=crossoverAuxiliary x y := by
  simp only [Crossover,gate_shared_equivalence]
  constructor
  · rintro ⟨⟨h0,a0⟩,⟨h1,a1⟩,⟨h2,a2⟩,⟨h3,a3⟩⟩
    have hxy : x'=x ∧ y'=y := by
      cases x <;> cases y <;> cases x' <;> cases y' <;> simp_all
    rcases hxy with ⟨rfl,rfl⟩
    refine ⟨rfl,rfl,h0,?_⟩
    funext k
    fin_cases k
    · exact a0
    · exact a1
    · exact a2
    · exact a3
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    simp [crossoverAuxiliary,eq_comm]

/-- All fifteen non-input bits, including the two output corners, are explicit. -/
abbrev CrossoverState := (Fin 3 → Bool) × (Fin 4 → Fin 3 → Bool)

def crossoverState (x y : Bool) : CrossoverState :=
  (![x,y,decide (x=y)],crossoverAuxiliary x y)

def CrossoverAccepts (x y : Bool) (s : CrossoverState) : Prop :=
  Crossover x y (s.1 0) (s.1 1) (s.1 2) s.2

theorem crossover_state_iff (x y : Bool) (s : CrossoverState) :
    CrossoverAccepts x y s ↔ s=crossoverState x y := by
  rw [CrossoverAccepts,crossover_iff]
  constructor
  · rintro ⟨hx,hy,he,ha⟩
    apply Prod.ext
    · funext k
      fin_cases k
      · exact hx
      · exact hy
      · exact he
    · exact ha
  · rintro rfl
    exact ⟨rfl,rfl,rfl,rfl⟩

def crossoverEquivUnit (x y : Bool) : {s : CrossoverState // CrossoverAccepts x y s} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨crossoverState x y,(crossover_state_iff x y _).mpr rfl⟩
  left_inv s := by
    apply Subtype.ext
    exact ((crossover_state_iff x y s.val).mp s.property).symm
  right_inv _ := rfl

theorem crossover_count (x y : Bool) : Fintype.card {s : CrossoverState // CrossoverAccepts x y s}=1 :=
  (Fintype.card_congr (crossoverEquivUnit x y)).trans (by simp)

end PlanarHom.ParsimoniousNorOneInThree
