import PlanarHom.RectangularWeightedNormNormalization
import PlanarHom.RectangularTwinQuotient
import PlanarHom.Boolean
import PlanarHom.CommonWeightedAmplitudeCoordinates

noncomputable section
set_option maxHeartbeats 500000
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularBackgroundWeightedReconstruction
open RectangularWeightedNormNormalization RectangularTwinQuotient CommonWeightedAmplitudeCoordinates
variable {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] {d : ℕ}

def rowMass (V : Matrix X Y ℝ) (μ : X → ℝ) (ν : Y → ℝ) (m : ℕ) (r : Rows (normalized V μ ν)) : ℝ :=
  ∑ x : {x // Quotient.mk (rowSetoid (normalized V μ ν)) x=r},μ x.val*(rowNorm V ν x.val)^(2*m)
def columnMass (V : Matrix X Y ℝ) (μ : X → ℝ) (ν : Y → ℝ) (m : ℕ) (s : Columns (normalized V μ ν)) : ℝ :=
  ∑ y : {y // Quotient.mk (columnSetoid (normalized V μ ν)) y=s},ν y.val*(columnNorm V μ y.val)^(2*m)

theorem row_amplitude_injective (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y)
    (hinj : Function.Injective V) (s : Rows (normalized V μ ν)) :
    Function.Injective (fun x : {x // Quotient.mk (rowSetoid (normalized V μ ν)) x=s} => rowNorm V ν x.val) := by
  intro x y he
  dsimp only at he
  apply Subtype.ext
  apply hinj
  have hn : normalized V μ ν x.val=normalized V μ ν y.val := Quotient.exact (x.property.trans y.property.symm)
  funext j
  rw [reconstruct V hV μ ν hμ hν x.val j,reconstruct V hV μ ν hμ hν y.val j,he,congrFun hn j]

theorem column_amplitude_injective (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y)
    (hinj : Function.Injective V.transpose) (s : Columns (normalized V μ ν)) :
    Function.Injective (fun y : {y // Quotient.mk (columnSetoid (normalized V μ ν)) y=s} => columnNorm V μ y.val) := by
  intro x y he
  dsimp only at he
  apply Subtype.ext
  apply hinj
  have hn : (normalized V μ ν).transpose x.val=(normalized V μ ν).transpose y.val := Quotient.exact (x.property.trans y.property.symm)
  funext i
  change V i x.val=V i y.val
  have hv : normalized V μ ν i x.val=normalized V μ ν i y.val := congrFun hn i
  rw [reconstruct V hV μ ν hμ hν i x.val,reconstruct V hV μ ν hμ hν i y.val,he,hv]

theorem original_weighted_amplitude_tensor (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (hinjR : Function.Injective V) (hinjC : Function.Injective V.transpose)
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y)
    (hmX : ∀ r s : Rows (normalized V μ ν),∀ m : ℕ,rowMass V μ ν m r=rowMass V μ ν m s)
    (hmY : ∀ r s : Columns (normalized V μ ν),∀ m : ℕ,columnMass V μ ν m r=columnMass V μ ν m s)
    (eR : Rows (normalized V μ ν) ≃ Boolean.Cube d) (eC : Columns (normalized V μ ν) ≃ Boolean.Cube d)
    (γ : ℝ) (hγ : 0<γ) (ρ : Fin d → ℝ)
    (hcore : ∀ r s,core (normalized V μ ν) r s=γ*Boolean.tensor ρ (eR r) (eC s)) :
    ∃ k l : ℕ,∃ a massX : Fin k → ℝ,∃ b massY : Fin l → ℝ,
    ∃ eX : X ≃ Fin k×Boolean.Cube d,∃ eY : Y ≃ Fin l×Boolean.Cube d,
      0<k ∧ 0<l ∧ (∀ i,0<a i) ∧ (∀ i,0<massX i) ∧ (∀ j,0<b j) ∧ (∀ j,0<massY j) ∧
        (∀ x y,V x y=a (eX x).1*b (eY y).1*Boolean.tensor ρ (eX x).2 (eY y).2) ∧
        (∀ x,μ x=massX (eX x).1) ∧ (∀ y,ν y=massY (eY y).1) := by
  let rmap : X → Rows (normalized V μ ν) := Quotient.mk _
  let cmap : Y → Columns (normalized V μ ν) := Quotient.mk _
  have hr : Function.Surjective rmap := fun r => ⟨r.out,Quotient.out_eq r⟩
  have hc : Function.Surjective cmap := fun s => ⟨s.out,Quotient.out_eq s⟩
  letI : Nonempty (Rows (normalized V μ ν)) := ⟨rmap (Classical.arbitrary X)⟩
  letI : Nonempty (Columns (normalized V μ ν)) := ⟨cmap (Classical.arbitrary Y)⟩
  obtain ⟨k,a,massX,ex,hk,ha,hmx,hex,hax,hweightX⟩ := exists_common_weighted_chart rmap hr
    (rowNorm V ν) μ (rowNorm_pos V hV ν hν) hμ (row_amplitude_injective V hV μ ν hμ hν hinjR) (by
      intro s t m
      convert hmX s t m using 1 <;> apply Finset.sum_congr (by ext x; simp) <;> intro x hx <;> rfl)
  obtain ⟨l,b,massY,ey,hl,hb,hmy,hey,hby,hweightY⟩ := exists_common_weighted_chart cmap hc
    (columnNorm V μ) ν (columnNorm_pos V hV μ hμ) hν (column_amplitude_injective V hV μ ν hμ hν hinjC) (by
      intro s t m
      convert hmY s t m using 1 <;> apply Finset.sum_congr (by ext x; simp) <;> intro x hx <;> rfl)
  let eX : X ≃ Fin k×Boolean.Cube d := ex.trans
    ((Equiv.prodCongr eR (Equiv.refl (Fin k))).trans (Equiv.prodComm _ _))
  let eY : Y ≃ Fin l×Boolean.Cube d := ey.trans
    ((Equiv.prodCongr eC (Equiv.refl (Fin l))).trans (Equiv.prodComm _ _))
  refine ⟨k,l,(fun i => γ*a i),massX,b,massY,eX,eY,hk,hl,(fun i => mul_pos hγ (ha i)),hmx,hb,hmy,?_,hweightX,hweightY⟩
  intro x y
  have hsource : V x y=rowNorm V ν x*columnNorm V μ y*
      core (normalized V μ ν) (rmap x) (cmap y) := by
    change V x y=rowNorm V ν x*columnNorm V μ y*
      core (normalized V μ ν) (Quotient.mk _ x) (Quotient.mk _ y)
    rw [core_entry]
    exact reconstruct V hV μ ν hμ hν x y
  have hv := hsource.trans
    (congrArg₂ (fun u v : ℝ => u*v)
      (congrArg₂ (fun u v : ℝ => u*v) (hax x) (hby y)) (hcore (rmap x) (cmap y)))
  change V x y=(γ*a (ex x).2)*b (ey y).2*Boolean.tensor ρ (eR (ex x).1) (eC (ey y).1)
  have heq : Boolean.tensor ρ (eR (ex x).1) (eC (ey y).1)=
      Boolean.tensor ρ (eR (rmap x)) (eC (cmap y)) :=
    congrArg₂ (Boolean.tensor ρ) (congrArg eR (hex x)) (congrArg eC (hey y))
  rw [heq]
  exact hv.trans (by ring)

theorem core_no_proportional_rows (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y)
    (r r' : Rows (normalized V μ ν)) (t : ℝ)
    (h : ∀ s,core (normalized V μ ν) r s=t*core (normalized V μ ν) r' s) : t=1 ∧ r=r' := by
  have hh : ∀ y,normalized V μ ν r.out y=t*normalized V μ ν r'.out y := by
    intro y
    simpa only [core_mk_column] using h (Quotient.mk (columnSetoid (normalized V μ ν)) y)
  have ht := (normalized_proportional_rows V hV μ ν hμ hν r.out r'.out t hh).1
  refine ⟨ht,core_rows_injective _ (funext (fun s => ?_))⟩
  simpa only [ht,one_mul] using h s

theorem core_no_proportional_columns (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y)
    (s s' : Columns (normalized V μ ν)) (t : ℝ)
    (h : ∀ r,core (normalized V μ ν) r s=t*core (normalized V μ ν) r s') : t=1 ∧ s=s' := by
  have hh : ∀ x,normalized V μ ν x s.out=t*normalized V μ ν x s'.out := by
    intro x
    simpa only [core_mk_row] using h (Quotient.mk (rowSetoid (normalized V μ ν)) x)
  have ht := (normalized_proportional_columns V hV μ ν hμ hν s.out s'.out t hh).1
  refine ⟨ht,core_columns_injective _ (funext (fun r => ?_))⟩
  simpa only [ht,one_mul] using h r

end PlanarHom.RectangularBackgroundWeightedReconstruction
