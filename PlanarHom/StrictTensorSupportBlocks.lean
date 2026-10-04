import PlanarHom.RectangularGramRoots
import PlanarHom.PositivePrincipalSubmatrix
import PlanarHom.SupportBlockSemantics

/-! NEW pure support-block data for §7, with strict Ising parameters. Taking a
positive entrywise root is a numerical identity, not an oracle operation. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.StrictTensorSupportBlocks
open Boolean
variable {I V : Type} [Fintype I] [Fintype V]

def Form (M : Matrix I I ℝ) : Prop :=
  ∃d : ℕ, ∃e : I ≃ Cube d, ∃γ : ℝ, ∃ρ : Fin d → ℝ,
    0<γ ∧ (∀r,0<ρ r ∧ ρ r<1) ∧ ∀i j,M i j=γ*tensor ρ (e i) (e j)

def Blocks (G : SimpleGraph V) (M : Matrix V V ℝ) : Prop :=
  ∀c : G.ConnectedComponent,Form (fun i j : c.supp=>M i.val j.val)

theorem Form.positive {M : Matrix I I ℝ} (h : Form M) : ∀i j,0<M i j := by
  obtain ⟨d,e,γ,ρ,hγ,hρ,hm⟩ := h
  intro i j
  rw [hm]
  exact mul_pos hγ (tensor_pos (fun r=>(hρ r).1) _ _)

theorem Form.posDef {M : Matrix I I ℝ} (h : Form M) : M.PosDef := by
  obtain ⟨d,e,γ,ρ,hγ,hρ,hm⟩ := h
  let T : Matrix (Cube d) (Cube d) ℝ := γ • tensor ρ
  have hp : T.PosDef := (tensor_posDef (fun r=>(hρ r).1) (fun r=>(hρ r).2)).smul hγ
  have hs := posDef_principal T hp e e.injective
  have he : M=T.submatrix e e := funext (fun i=>funext (hm i))
  rwa [←he] at hs

theorem Form.diagonal_constant {M : Matrix I I ℝ} (h : Form M) : ∀i j,M i i=M j j := by
  obtain ⟨d,e,γ,ρ,hγ,hρ,hm⟩ := h
  intro i j
  simp only [hm,tensor_diag,mul_one]

theorem root_form (M : Matrix I I ℝ) (hnn : ∀i j,0≤M i j) (p : ℕ) (hp : p≠0)
    (h : Form (fun i j=>M i j^p)) : Form M := by
  obtain ⟨d,e,γ,ρ,hγ,hρ,hm⟩ := h
  dsimp only at hm
  have hpos : ∀i j,0<M i j := by
    intro i j
    have hn : M i j≠0 := by
      intro hz
      have he := hm i j
      rw [hz,zero_pow hp] at he
      exact (ne_of_gt (mul_pos hγ (tensor_pos (fun r=>(hρ r).1) _ _))) he.symm
    exact lt_of_le_of_ne (hnn i j) hn.symm
  let C : Matrix (Cube d) (Cube d) ℝ := fun i j=>M (e.symm i) (e.symm j)
  have hC : ∀i j,C i j^p=γ*tensor ρ i j := by
    intro i j
    simpa only [e.apply_symm_apply] using hm (e.symm i) (e.symm j)
  have hr := RectangularGramRoots.positive_tensor_root C (fun i j=>hpos _ _) p hp γ ρ hρ hC
  refine ⟨d,e,γ^((p:ℝ)⁻¹),RectangularGramRoots.rootParameters ρ p,
    Real.rpow_pos_of_pos hγ _,RectangularGramRoots.root_range ρ hρ p hp,?_⟩
  intro i j
  simpa only [C,e.symm_apply_apply] using hr (e i) (e j)

theorem Blocks.root {p : ℕ} {G : SimpleGraph V} {M : Matrix V V ℝ}
    (h : Blocks G (fun i j=>M i j^p)) (hnn : ∀i j,0≤M i j) (hp : p≠0) : Blocks G M := by
  intro c
  exact root_form (fun i j : c.supp=>M i.val j.val) (fun i j=>hnn _ _) p hp (h c)

end PlanarHom.StrictTensorSupportBlocks
