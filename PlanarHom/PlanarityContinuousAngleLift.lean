import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting

/-!
# NEW continuous real-angle lifts on a square

This is the missing elementary lifting ingredient for an alternating-endpoint
half-plane crossing obstruction. No Jordan or planarity assertion is an input.
-/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.PlanarityContinuousAngleLift

/-- Lift a path through the additive circle, using actual local sections and a
finite subdivision of the parameter interval. -/
theorem exists_path_lift (p : ℝ) [Fact (0 < p)] (γ : C(I, AddCircle p))
    (e : ℝ) (he : (e : AddCircle p) = γ 0) :
    ∃ Γ : C(I, ℝ), (∀ t, (Γ t : AddCircle p) = γ t) ∧ Γ 0 = e := by
  have homeo := AddCircle.isLocalHomeomorph_coe p
  have hsur : Function.Surjective ((↑) : ℝ → AddCircle p) := QuotientAddGroup.mk_surjective
  choose r hr using hsur
  choose q hq hpq using fun x => homeo (r x)
  have htgt (x : AddCircle p) : x ∈ (q x).target := by
    have h := (q x).map_source (hq x)
    rw [← hpq x, hr x] at h
    exact h
  obtain ⟨t, t0, tmono, ⟨nmax, hmax⟩, tsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun x => (q x).open_target.preimage γ.continuous)
      (fun s _ => Set.mem_iUnion.mpr ⟨γ s, htgt _⟩)
  suffices ∀ n, ∃ Γ : I → ℝ, ContinuousOn Γ (Set.Icc 0 (t n)) ∧
      (∀ s ∈ Set.Icc 0 (t n), (Γ s : AddCircle p) = γ s) ∧ Γ 0 = e by
    obtain ⟨Γ, hc, hl, hz⟩ := this nmax
    rw [hmax _ le_rfl] at hc hl
    refine ⟨⟨Γ, continuousOn_univ.mp ?_⟩, fun s => hl s ⟨bot_le, le_top⟩, hz⟩
    convert hc using 1
    symm
    rw [Set.eq_univ_iff_forall]
    exact fun s => ⟨bot_le, le_top⟩
  intro n
  induction n with
  | zero =>
      refine ⟨fun _ => e, continuous_const.continuousOn, ?_, rfl⟩
      intro s hs
      rw [t0, Set.Icc_self, Set.mem_singleton_iff] at hs
      subst s
      exact he
  | succ n ih =>
      obtain ⟨Γ, hc, hl, hz⟩ := ih
      obtain ⟨x, hx⟩ := tsub n
      have hn : γ (t n) ∈ (q x).target := hx ⟨le_rfl, tmono n.le_succ⟩
      have hnΓ := hl (t n) ⟨t0 ▸ tmono n.zero_le, le_rfl⟩
      have hsection {s : I} (hs : γ s ∈ (q x).target) :
          ((q x).symm (γ s) : AddCircle p) = γ s := by
        exact (congr_fun (hpq x) ((q x).symm (γ s))).trans ((q x).right_inv hs)
      refine ⟨fun s => if s ≤ t n then Γ s
        else (q x).symm (γ s) + (Γ (t n) - (q x).symm (γ (t n))),
        .if (fun s hs => ?_) (hc.mono fun s h => ?_) ?_, ?_, ?_⟩
      · cases frontier_Iic_subset _ hs.2
        ring
      · rw [closure_le_eq continuous_id' continuous_const] at h
        exact ⟨h.1.1, h.2⟩
      · apply ContinuousOn.add _ continuousOn_const
        apply (q x).continuousOn_invFun.comp γ.continuous.continuousOn
        intro s h
        simp only [not_le] at h
        exact hx ⟨closure_lt_subset_le continuous_const continuous_subtype_val h.2, h.1.2⟩
      · intro s hs
        dsimp only
        split_ifs with h
        · exact hl s ⟨hs.1, h⟩
        · rw [AddCircle.coe_add, AddCircle.coe_sub, hsection (hx ⟨le_of_not_ge h, hs.2⟩),
            hnΓ, hsection hn]
          simp
      · dsimp only
        rwa [if_pos (t0 ▸ tmono n.zero_le)]

/-- Every continuous circle-valued map on the square has a continuous real lift.
The construction first lifts the left edge, then all horizontal paths; the
local-homeomorphism continuation theorem proves joint continuity. -/
theorem exists_square_lift (p : ℝ) [Fact (0 < p)] (f : C(I × I, AddCircle p)) :
    ∃ F : C(I × I, ℝ), ∀ st, (F st : AddCircle p) = f st := by
  obtain ⟨e, he⟩ := QuotientAddGroup.mk_surjective (f (0,0))
  obtain ⟨left, hl, _⟩ := exists_path_lift p
    ⟨fun t => f (0,t), f.continuous.comp (continuous_const.prodMk continuous_id)⟩ e he
  have hpaths (t : I) := exists_path_lift p
    (⟨fun s => f (s,t), f.continuous.comp (continuous_id.prodMk continuous_const)⟩)
    (left t) (hl t)
  choose paths hpaths hzero using hpaths
  let F : I × I → ℝ := fun st => paths st.2 st.1
  have hF : Continuous F := (AddCircle.isLocalHomeomorph_coe p).continuous_lift
    (T2Space.isSeparatedMap _) f (funext fun st => hpaths st.2 st.1)
    (by simpa only [F, hzero] using left.continuous) (fun t => (paths t).continuous)
  exact ⟨⟨F,hF⟩,fun st => hpaths st.2 st.1⟩

/-- The increments of two real lifts of one circle-valued path agree. -/
theorem lift_increment_eq (p : ℝ) [Fact (0 < p)] (f g : C(I, ℝ))
    (h : ∀ t, (f t : AddCircle p) = (g t : AddCircle p)) :
    f 1 - f 0 = g 1 - g 0 := by
  have hc : Continuous (fun t => f t - g t) := f.continuous.sub g.continuous
  have he := (T2Space.isSeparatedMap ((↑) : ℝ → AddCircle p)).const_of_comp
    (AddCircle.isLocalHomeomorph_coe p).isLocallyInjective hc
    (fun t u => by simp only [AddCircle.coe_sub, h, sub_self]) (1 : I) 0
  linarith

/-- Four continuous real branches on the edges of a square obey the exact
zero total increment identity. -/
theorem square_boundary_increment (p : ℝ) [Fact (0 < p)]
    (f : C(I × I, AddCircle p)) (bottom top left right : C(I, ℝ))
    (hb : ∀ t, (bottom t : AddCircle p) = f (t,0))
    (ht : ∀ t, (top t : AddCircle p) = f (t,1))
    (hl : ∀ t, (left t : AddCircle p) = f (0,t))
    (hr : ∀ t, (right t : AddCircle p) = f (1,t)) :
    (bottom 1-bottom 0) + (right 1-right 0) =
      (left 1-left 0) + (top 1-top 0) := by
  obtain ⟨F,hF⟩ := exists_square_lift p f
  have hb' := lift_increment_eq p bottom
    ⟨fun t => F (t,0), F.continuous.comp (continuous_id.prodMk continuous_const)⟩
    (fun t => (hb t).trans (hF (t,0)).symm)
  have ht' := lift_increment_eq p top
    ⟨fun t => F (t,1), F.continuous.comp (continuous_id.prodMk continuous_const)⟩
    (fun t => (ht t).trans (hF (t,1)).symm)
  have hl' := lift_increment_eq p left
    ⟨fun t => F (0,t), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
    (fun t => (hl t).trans (hF (0,t)).symm)
  have hr' := lift_increment_eq p right
    ⟨fun t => F (1,t), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
    (fun t => (hr t).trans (hF (1,t)).symm)
  dsimp at hb' ht' hl' hr'
  linarith

end PlanarHom.PlanarityContinuousAngleLift
