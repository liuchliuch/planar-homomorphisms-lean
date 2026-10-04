import PlanarHom.PolygonalSignedStripWidths

/-! NEW proof: center compatibility between opposite signed strip sides.
These numerical lemmas prevent independent positive/negative ribbons from
crossing one another; no local-neighborhood or face-topology conclusion is assumed. -/
noncomputable section
open Set unitInterval Filter
open scoped Topology Convex
namespace PlanarHom.Polygonal
open MultiGraph

private theorem combo_cross (D A B : Plane) (t : ℝ) :
    cross D (A+t • (B-A)) = (1-t)*cross D A+t*cross D B := by
  simp only [cross_add_right,cross_smul_right,cross_sub_right]
  ring

private theorem combo_zero_of_cross_zero (D A B : Plane)
    (hA : A=0 ∨ 0<cross D A) (hB : B=0 ∨ 0<cross D B) (t : I)
    (hz : cross D (A+(t : ℝ) • (B-A))=0) : A+(t : ℝ) • (B-A)=0 := by
  rw [combo_cross] at hz
  rcases hA with rfl | hA <;> rcases hB with rfl | hB
  · simp
  · have ht : (t : ℝ)=0 := by simp only [cross_zero_right,mul_zero,zero_add] at hz; nlinarith
    simp [ht]
  · have ht : (t : ℝ)=1 := by simp only [cross_zero_right,mul_zero,add_zero] at hz; nlinarith
    simp [ht]
  · have hh := closed_combo_pos hA hB t.2.1 t.2.2
    linarith

private theorem strip_center_eq_of_cross_zero (P Q A B : Plane)
    (hA : A=0 ∨ 0<cross (Q-P) A) (hB : B=0 ∨ 0<cross (Q-P) B) (p : I × I)
    (hz : (p.2 : ℝ)*cross (Q-P) (A+(p.1 : ℝ) • (B-A))=0) :
    stripMap P Q A B p = AffineMap.lineMap P Q (p.1 : ℝ) := by
  rcases mul_eq_zero.mp hz with hs | hnormal
  · simp [stripMap,strip,hs,AffineMap.lineMap_apply_module']; module
  · have hn := combo_zero_of_cross_zero (Q-P) A B hA hB p.1 hnormal
    change P+(p.1 : ℝ) • (Q-P)+(p.2 : ℝ) • (A+(p.1 : ℝ) • (B-A)) = _
    rw [hn,smul_zero,add_zero]
    rw [AffineMap.lineMap_apply_module']; exact add_comm _ _

/-- Opposite strips over the same center segment can meet only over a common
center point, including genuinely pinched endpoint sides. -/
theorem centersAgree_opposite_self (P Q A B : Plane)
    (hA : A=0 ∨ 0<cross (Q-P) A) (hB : B=0 ∨ 0<cross (Q-P) B) :
    StripCentersAgree P Q A B P Q (-A) (-B) := by
  intro p q heq
  have ha : 0 ≤ cross (Q-P) A := hA.elim (fun h => by simp [h]) le_of_lt
  have hb : 0 ≤ cross (Q-P) B := hB.elim (fun h => by simp [h]) le_of_lt
  have hcp : 0 ≤ cross (Q-P) (A+(p.1 : ℝ) • (B-A)) := by
    rw [combo_cross]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr p.1.2.2) ha) (mul_nonneg p.1.2.1 hb)
  have hcq : 0 ≤ cross (Q-P) (A+(q.1 : ℝ) • (B-A)) := by
    rw [combo_cross]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr q.1.2.2) ha) (mul_nonneg q.1.2.1 hb)
  have he := congrArg (fun x => cross (Q-P) (x-P)) heq
  have hformula : (p.2 : ℝ)*cross (Q-P) (A+(p.1 : ℝ) • (B-A)) =
      -((q.2 : ℝ)*cross (Q-P) (A+(q.1 : ℝ) • (B-A))) := by
    simp only [stripMap,ContinuousMap.coe_mk,strip,cross_add_right,
      cross_smul_right,cross_self,mul_zero,cross_sub_right,cross_neg_right] at he ⊢
    nlinarith [he]
  have hp0 : (p.2 : ℝ)*cross (Q-P) (A+(p.1 : ℝ) • (B-A))=0 := by
    nlinarith [mul_nonneg p.2.2.1 hcp,mul_nonneg q.2.2.1 hcq]
  have hq0 : (q.2 : ℝ)*cross (Q-P) (A+(q.1 : ℝ) • (B-A))=0 := by linarith
  have hpcenter := strip_center_eq_of_cross_zero P Q A B hA hB p hp0
  have hqcenter : stripMap P Q (-A) (-B) q = AffineMap.lineMap P Q (q.1 : ℝ) := by
    rcases mul_eq_zero.mp hq0 with hs | hn
    · simp [stripMap,strip,hs,AffineMap.lineMap_apply_module']; module
    · have hz := combo_zero_of_cross_zero (Q-P) A B hA hB q.1 hn
      have hz' : -A+(q.1 : ℝ) • (-B - -A)=0 := by
        calc
          _ = -(A+(q.1 : ℝ) • (B-A)) := by module
          _ = 0 := by rw [hz]; simp
      change P+(q.1 : ℝ) • (Q-P)+(q.2 : ℝ) • (-A+(q.1 : ℝ) • (-B - -A)) = _
      rw [hz',smul_zero,add_zero]
      rw [AffineMap.lineMap_apply_module']; exact add_comm _ _
  exact hpcenter.symm.trans (heq.trans hqcenter)

/-- At an actual polygonal corner the separator perpendicular to the shared
normal works with independently signed widths on its two incident pieces. -/
theorem eventually_centersAgree_adjacent_signed (P Q R A N B : Plane) (c d : ℝ)
    (hP : 0 < cross (Q-P) N) (hQ : 0 < cross (R-Q) N) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      StripCentersAgree P Q (ε • (c • A)) (ε • (c • N))
        Q R (ε • (d • N)) (ε • (d • B)) := by
  have hlim (D M : Plane) : Tendsto (fun ε : ℝ => cross (D+ε • M) N)
      (𝓝 0) (𝓝 (cross D N)) := by
    have hc : Continuous (fun ε : ℝ => cross (D+ε • M) N) := by unfold cross; fun_prop
    simpa using hc.continuousAt.tendsto (x := (0 : ℝ))
  filter_upwards [(hlim (Q-P) (c • (N-A))).eventually_const_lt hP,
    (hlim (R-Q) (d • (B-N))).eventually_const_lt hQ] with ε hεP hεQ
  intro p q heq
  have hp' : 0 < cross (Q-P+(p.2 : ℝ) • (ε • (c • (N-A)))) N := by
    rw [cross_interpolate]
    exact closed_combo_pos hP hεP p.2.2.1 p.2.2.2
  have hq' : 0 < cross (R-Q+(q.2 : ℝ) • (ε • (d • (B-N)))) N := by
    rw [cross_interpolate]
    exact closed_combo_pos hQ hεQ q.2.2.1 q.2.2.2
  have hc := congrArg (fun x => cross (x-Q) N) heq
  have hcalc : ((p.1 : ℝ)-1)*cross (Q-P+(p.2 : ℝ) • (ε • (c • (N-A)))) N =
      (q.1 : ℝ)*cross (R-Q+(q.2 : ℝ) • (ε • (d • (B-N)))) N := by
    simp only [stripMap,ContinuousMap.coe_mk,strip,cross,Prod.fst_add,Prod.snd_add,
      Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] at hc ⊢
    nlinarith [hc]
  have hp1 : (p.1 : ℝ)=1 := by nlinarith [p.1.2.2,q.1.2.1]
  have hq0 : (q.1 : ℝ)=0 := by nlinarith
  simp [hp1,hq0]

/-- Independently signed normals at distinct host rays are separated by the
existing geometric ray theorem; the host offsets are literally zero. -/
theorem eventually_centersAgree_at_host_twoNormals (P Q R S X : Plane) (N M : Plane → Plane)
    (hPQ : P ≠ Q) (hRS : R ≠ S) (hNX : N X = 0) (hMX : M X=0)
    (hleft : P=X ∨ Q=X) (hright : R=X ∨ S=X)
    (hinter : ∀ z, z ∈ [P -[ℝ] Q] → z ∈ [R -[ℝ] S] → z=X) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      StripCentersAgree P Q (ε • N P) (ε • N Q) R S (ε • M R) (ε • M S) := by
  rcases hleft with rfl | rfl
  · rcases hright with rfl | rfl
    · simpa only [hNX,hMX,smul_zero] using
        eventually_centersAgree_rays R Q S (N Q) (M S) hPQ hRS hinter
    · have hi : ∀ z, z ∈ [S -[ℝ] Q] → z ∈ [S -[ℝ] R] → z=S := by
        intro z hz hz'
        exact hinter z hz (by simpa only [segment_symm] using hz')
      filter_upwards [eventually_centersAgree_rays S Q R (N Q) (M R) hPQ hRS.symm hi] with ε hε
      simpa only [hNX,hMX,smul_zero] using hε.reverse_right
  · rcases hright with rfl | rfl
    · have hi : ∀ z, z ∈ [R -[ℝ] P] → z ∈ [R -[ℝ] S] → z=R := by
        intro z hz hz'
        exact hinter z (by simpa only [segment_symm] using hz) hz'
      filter_upwards [eventually_centersAgree_rays R P S (N P) (M S) hPQ.symm hRS hi] with ε hε
      simpa only [hNX,hMX,smul_zero] using hε.reverse_left
    · have hi : ∀ z, z ∈ [S -[ℝ] P] → z ∈ [S -[ℝ] R] → z=S := by
        intro z hz hz'
        exact hinter z (by simpa only [segment_symm] using hz) (by simpa only [segment_symm] using hz')
      filter_upwards [eventually_centersAgree_rays S P R (N P) (M R) hPQ.symm hRS.symm hi] with ε hε
      simpa only [hNX,hMX,smul_zero] using hε.reverse_left.reverse_right


/-- One sufficiently small width gives cross-side center compatibility for
 every pair of actual pieces of a finite polygonal drawing. -/
theorem eventually_all_opposite_strip_centers (S : Finset (Plane × Plane)) (H : Set Plane)
    (N : Plane → Plane) (hcorner : TwoValentCorners (S : Set (Plane × Plane)) H)
    (hpair : EndpointIntersections (S : Set (Plane × Plane)))
    (hne : ∀ e ∈ S, e.1 ≠ e.2)
    (hzero : ∀ x ∈ H, N x=0)
    (hout : ∀ a b, (a,b) ∈ S → a ∉ H → 0<cross (b-a) (N a))
    (hin : ∀ a b, (a,b) ∈ S → b ∉ H → 0<cross (b-a) (N b)) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, ∀ e ∈ S, ∀ f ∈ S,
      StripCentersAgree e.1 e.2 (ε • N e.1) (ε • N e.2)
        f.1 f.2 (ε • -N f.1) (ε • -N f.2) := by
  apply (Filter.eventually_all_finset S).mpr
  intro e he
  apply (Filter.eventually_all_finset S).mpr
  intro f hf
  by_cases hef : e=f
  · subst f
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hpos : 0<ε := hε
    have hA : ε • N e.1=0 ∨ 0<cross (e.2-e.1) (ε • N e.1) := by
      by_cases hh : e.1 ∈ H
      · exact Or.inl (by simp [hzero e.1 hh])
      · exact Or.inr (by simpa using mul_pos hpos (hout e.1 e.2 he hh))
    have hB : ε • N e.2=0 ∨ 0<cross (e.2-e.1) (ε • N e.2) := by
      by_cases hh : e.2 ∈ H
      · exact Or.inl (by simp [hzero e.2 hh])
      · exact Or.inr (by simpa using mul_pos hpos (hin e.1 e.2 he hh))
    simpa only [smul_neg] using centersAgree_opposite_self e.1 e.2 (ε • N e.1) (ε • N e.2) hA hB
  · rcases hpair e he f hf hef with hdis | ⟨X,hleft,hright,hinter⟩
    · exact (eventually_centersAgree_of_disjoint e.1 e.2 f.1 f.2
        (N e.1) (N e.2) (-N f.1) (-N f.2) hdis).filter_mono nhdsWithin_le_nhds
    · by_cases hX : X ∈ H
      · exact (eventually_centersAgree_at_host_twoNormals e.1 e.2 f.1 f.2 X N (fun x => -N x)
          (hne e he) (hne f hf) (hzero X hX) (by simp [hzero X hX])
          hleft hright hinter).filter_mono nhdsWithin_le_nhds
      · obtain ⟨P,Q,_,_,_,hsucc,hpred⟩ := hcorner X hX ⟨e.1,e.2,he,hleft⟩
        rcases hleft with heX | heX <;> rcases hright with hfX | hfX
        · exact (hef (Prod.ext (heX.trans hfX.symm)
            ((hsucc _ _ he heX).trans (hsucc _ _ hf hfX).symm))).elim
        · have hcrossF : 0<cross (X-f.1) (N X) := by
            simpa only [hfX] using hin _ _ hf (by simpa only [hfX] using hX)
          have hcrossE : 0<cross (e.2-X) (N X) := by
            simpa only [heX] using hout _ _ he (by simpa only [heX] using hX)
          filter_upwards [(eventually_centersAgree_adjacent_signed f.1 X e.2
            (N f.1) (N X) (N e.2) (-1) 1 hcrossF hcrossE).filter_mono nhdsWithin_le_nhds] with ε hε
          simpa only [heX,hfX,neg_one_smul,one_smul] using hε.symm
        · have hcrossE : 0<cross (X-e.1) (N X) := by
            simpa only [heX] using hin _ _ he (by simpa only [heX] using hX)
          have hcrossF : 0<cross (f.2-X) (N X) := by
            simpa only [hfX] using hout _ _ hf (by simpa only [hfX] using hX)
          filter_upwards [(eventually_centersAgree_adjacent_signed e.1 X f.2
            (N e.1) (N X) (N f.2) 1 (-1) hcrossE hcrossF).filter_mono nhdsWithin_le_nhds] with ε hε
          simpa only [heX,hfX,neg_one_smul,one_smul] using hε
        · exact (hef (Prod.ext ((hpred _ _ he heX).trans (hpred _ _ hf hfX).symm)
            (heX.trans hfX.symm))).elim

end PlanarHom.Polygonal
