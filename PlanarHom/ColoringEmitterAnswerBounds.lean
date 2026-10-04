import PlanarHom.ColoringEmitterRecoveryMachines
import PlanarHom.ProperColoringNaturalReduction
import PlanarHom.BinaryGcdBits

/-! NEW linear binary-answer bounds for the actual natural three-color oracle. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open Complexity ProperColoringPottsReduction

theorem properColoringCount_le_pow {V E : Type} [Fintype V] [Fintype E]
    (G : MultiGraph V E) (q : ℕ) : properColoringCount G q≤q^Fintype.card V := by
  simpa [properColoringCount] using
    (Fintype.card_subtype_le (fun σ : V→Fin q=>∀e,σ (G.src e)≠σ (G.dst e)))

theorem properColoringCount_code_bound {V E : Type} [Fintype V] [Fintype E]
    (G : MultiGraph V E) :
    (BitEncoding.nat.encode (properColoringCount G 3)).length≤2*Fintype.card V+1 := by
  have h:=BinaryArithmetic.encodeNat_length_mono (properColoringCount_le_pow G 3)
  change (BitEncoding.nat.encode (properColoringCount G 3)).length≤
    (BitEncoding.nat.encode (3^Fintype.card V)).length at h
  have hp:=nat_pow_code_bound 3 (Fintype.card V)
  have h3 : (BitEncoding.nat.encode 3).length≤2 := by
    change (Computability.encodeNat 3).length≤2
    rw [BinaryArithmetic.encodeNat_length]
    exact Nat.size_le.mpr (by norm_num)
  have hm:=Nat.mul_le_mul_left (Fintype.card V) h3
  omega

theorem totalColorings_code_bound (g : MixedCode) :
    (BitEncoding.nat.encode (totalColorings 3 g)).length≤2*g.vertices+1 := by
  by_cases hg:g.Valid 1 0
  · simpa [totalColorings,hg] using properColoringCount_code_bound (g.toMultiGraph hg)
  · simp only [totalColorings,dif_neg hg]
    exact (Complexity.encodeNat_length_le 0).trans (by omega)

end PlanarHom.ColoringEmitter
