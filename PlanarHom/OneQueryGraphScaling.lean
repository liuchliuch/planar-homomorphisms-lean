import PlanarHom.GraphNonadaptiveReduction
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.SourceSimulationOutputBounds

/-! A genuine single-query scaling compiler for full raw graph-code promises.
The scale is produced by an actual fixed-field machine. The one oracle answer,
all intermediate words and exact field multiplication are charged. -/
noncomputable section
namespace PlanarHom.OneQueryGraphScaling
open Complexity Complexity.MixedCode PlanarHom.MachineComposition
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

private def rawView (H : MixedCode → Prop) (raw : Bits)
    (h : ∃ g, encoding.decode raw = some g ∧ H g) : BitEncoding.ValidWord encoding :=
  ⟨raw, by obtain ⟨g, hd, _⟩ := h; exact ⟨g, hd⟩⟩

private theorem rawView_property (H : MixedCode → Prop) (raw : Bits)
    (h : ∃ g, encoding.decode raw = some g ∧ H g) : H (rawView H raw h).value := by
  obtain ⟨g, hd, hg⟩ := h
  have hv : (rawView H raw ⟨g, hd, hg⟩).value = g := BitEncoding.ValidWord.value_eq hd
  rw [hv]
  exact hg

/-- Exactly one unchanged decoded graph is queried. Input normalization handles
every successful alternate raw encoding; no component advice is supplied. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (H : MixedCode → Prop) (target source : PromiseProblem)
    (ht : ∀ raw, target.valid raw ↔ ∃ g, encoding.decode raw = some g ∧ H g)
    (hs : ∀ raw, source.valid raw ↔ ∃ g, encoding.decode raw = some g ∧ H g)
    (value answer scale : MixedCode → K)
    (hv : ∀ raw g, encoding.decode raw = some g → H g →
      target.value raw = (numberFieldEncoding basis).encode (value g))
    (ha : ∀ raw g, encoding.decode raw = some g → H g →
      source.value raw = (numberFieldEncoding basis).encode (answer g))
    (hscale : FP encoding (numberFieldEncoding basis) scale)
    (correct : ∀ g, H g → scale g * answer g = value g)
    (p : Polynomial ℕ)
    (bound : ∀ raw, source.valid raw → (source.value raw).length ≤ p.eval raw.length) :
    PromisePolyTimeTuringReduction target source := by
  let prepare := fun g : MixedCode => (scale g, [g])
  have hp : FP encoding ((numberFieldEncoding basis).prod encoding.list) prepare := by
    have hl : FP encoding encoding.list (fun g : MixedCode => [g]) :=
      ((fp_id encoding).pair (fp_const encoding encoding.list [])).comp
        (ListMutationMachines.fp_cons encoding)
    exact hscale.pair hl
  let pre := composeComputers normalizer (Classical.choice hp)
  let recover := fun z : K × List K => z.1 * z.2.prod
  apply nonadaptiveReduction (p := p)
    (BitEncoding.ValidWord.encoding encoding) (numberFieldEncoding basis) encoding
    (numberFieldEncoding basis) (numberFieldEncoding basis)
    target source (prepare ∘ BitEncoding.ValidWord.value) answer recover pre
    (Classical.choice (MaterializedFieldListMachines.fp_fold_product basis))
    (fun raw h => rawView H raw ((ht raw).mp h)) (fun _ _ => rfl)
  · intro raw h query hquery
    have hg := rawView_property H raw ((ht raw).mp h)
    have he : query = (rawView H raw ((ht raw).mp h)).value := by
      simpa [prepare, Function.comp_def] using hquery
    subst query
    exact (hs _).mpr ⟨_, encoding.decode_encode _, hg⟩
  · intro query hq
    obtain ⟨g, hd, hg⟩ := (hs _).mp hq
    rw [encoding.decode_encode] at hd
    cases Option.some.inj hd
    exact ha _ query (encoding.decode_encode _) hg
  · intro raw h
    have hg := rawView_property H raw ((ht raw).mp h)
    change (numberFieldEncoding basis).encode
      (scale (rawView H raw ((ht raw).mp h)).value *
        ([answer (rawView H raw ((ht raw).mp h)).value]).prod) = _
    simp only [List.prod_cons, List.prod_nil, mul_one]
    rw [correct _ hg]
    exact (hv _ _ (BitEncoding.ValidWord.decode_raw _) hg).symm
  · exact bound

end PlanarHom.OneQueryGraphScaling
