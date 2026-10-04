import PlanarHom.PlanarFaceBridges
import PlanarHom.PlanarTruncation

/-!
# Compact complementary cores between disjoint terminal balls

An ordinary cofacial bridge can be trimmed between two sphere crossings. Its
compact middle avoids the entire original drawing, and its ends are ports of
the two terminal balls. Other vertex balls can then be shrunk around this core.
-/

noncomputable section
open Set unitInterval
open Classical
namespace PlanarHom.MultiGraph.PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- An actual complementary compact connected core with two terminal ports. -/
structure FaceBridgeCore (d : PlaneDrawing G) (u v : V) (r : ℝ) where
  left : Plane
  right : Plane
  core : Set Plane
  isCompact : IsCompact core
  isConnected : IsConnected core
  left_mem : left ∈ core
  right_mem : right ∈ core
  distinct : left ≠ right
  avoids : core ⊆ d.supportᶜ
  left_sphere : dist left (d.point u) = r
  right_sphere : dist right (d.point v) = r
  outside_left : ∀ x ∈ core, r ≤ dist x (d.point u)
  outside_right : ∀ x ∈ core, r ≤ dist x (d.point v)

/-- Last/first crossings retain only a bridge portion outside both terminal balls. -/
theorem NearFaceBridge.exists_core {d : PlaneDrawing G} {u v : V} {r : ℝ}
    (B : d.NearFaceBridge u v r) (hr : 0 < r)
    (hsep : 4*r < dist (d.point u) (d.point v)) :
    Nonempty (d.FaceBridgeCore u v r) := by
  let p := B.chain.strictPath
  let f : C(I,ℝ) := ⟨fun t => dist (p t) (d.point u),by fun_prop⟩
  let g : C(I,ℝ) := ⟨fun t => dist (p t) (d.point v),by fun_prop⟩
  have hf0 : f 0 < r := by simpa [f,p] using B.left_near
  have hg1 : g 1 < r := by simpa [g,p] using B.right_near
  have hg0 : r < g 0 := by
    have htri := dist_triangle (d.point u) B.left (d.point v)
    rw [dist_comm (d.point u) B.left] at htri
    dsimp [g,p]
    rw [B.chain.strictPath.source]
    linarith [B.left_near]
  obtain ⟨b,hb,hgb,hbefore⟩ := first_level_crossing g
    (show (0 : I) ≤ 1 from bot_le) hg0 hg1
  have hfb : r < f b := by
    have htri := dist_triangle (d.point u) (p b) (d.point v)
    rw [dist_comm (d.point u) (p b)] at htri
    change dist (p b) (d.point v) = r at hgb
    dsimp [f]
    linarith
  obtain ⟨a,ha,hfa,hafter⟩ := last_level_crossing f hb.1.le hf0 hfb
  let K := p '' Set.Icc a b
  have hi : ∀ t ∈ Set.Icc a b, Inside t := by
    intro t ht
    exact ⟨ha.1.trans_le ht.1,ht.2.trans_lt hb.2⟩
  have hinj := B.chain.strictPath_injective B.simple B.distinct
  refine ⟨⟨p a,p b,K,isCompact_Icc.image p.continuous,
    (isConnected_Icc ha.2.le).image _ p.continuous.continuousOn,
    ⟨a,⟨le_rfl,ha.2.le⟩,rfl⟩,⟨b,⟨ha.2.le,le_rfl⟩,rfl⟩,
    (hinj.ne ha.2.ne),?_,hfa,hgb,?_,?_⟩⟩
  · rintro x ⟨t,ht,rfl⟩
    exact B.avoids t (hi t ht)
  · rintro x ⟨t,ht,rfl⟩
    by_cases hta : t = a
    · subst t
      exact hfa.ge
    · exact (hafter t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta),ht.2⟩).le
  · rintro x ⟨t,ht,rfl⟩
    by_cases htb : t = b
    · subst t
      exact hgb.ge
    · exact (hbefore t ⟨(ha.1.trans_le ht.1).le,lt_of_le_of_ne ht.2 htb⟩).le

/-- Cofaciality in the original continuous drawing provides the separated core. -/
theorem Cofacial.exists_faceBridgeCore [Finite V] [Finite E] {d : PlaneDrawing G}
    {u v : V} (hface : d.Cofacial u v) (huv : u ≠ v) {r : ℝ} (hr : 0 < r)
    (hsep : 4*r < dist (d.point u) (d.point v)) :
    Nonempty (d.FaceBridgeCore u v r) := by
  obtain ⟨B⟩ := hface.exists_nearFaceBridge huv hr
  exact B.exists_core hr hsep

/-- Keep the two terminal radii while shrinking all other balls to avoid the
actual compact bridge. The radii are positive even at isolated vertices. -/
theorem FaceBridgeCore.exists_radii {d : PlaneDrawing G} {u v : V} {r : ℝ}
    (B : d.FaceBridgeCore u v r) (hr : 0 < r) :
    ∃ rho : V → ℝ, (∀ w, 0 < rho w) ∧ (∀ w, rho w ≤ r) ∧
      rho u = r ∧ rho v = r ∧ ∀ x ∈ B.core, ∀ w, rho w ≤ dist x (d.point w) := by
  have hlocal : ∀ w, ∃ s : ℝ, 0 < s ∧ Metric.ball (d.point w) s ⊆ B.coreᶜ := by
    intro w
    apply Metric.isOpen_iff.mp B.isCompact.isClosed.isOpen_compl
    exact fun hw => B.avoids hw (Or.inl ⟨w,rfl⟩)
  choose s hs hball using hlocal
  let rho : V → ℝ := fun w => if w = u ∨ w = v then r else min r (s w)
  have hpos : ∀ w, 0 < rho w := by
    intro w
    dsimp [rho]
    split
    · exact hr
    · exact lt_min hr (hs w)
  have hle : ∀ w, rho w ≤ r := by
    intro w
    dsimp [rho]
    split
    · exact le_rfl
    · exact min_le_left _ _
  refine ⟨rho,hpos,hle,by simp [rho],by simp [rho],?_⟩
  intro x hx w
  by_cases hu : w = u
  · subst w
    simpa [rho] using B.outside_left x hx
  by_cases hv : w = v
  · subst w
    simpa [rho] using B.outside_right x hx
  have hsx : s w ≤ dist x (d.point w) := by
    by_contra h
    exact hball w (lt_of_not_ge h) hx
  exact (show rho w ≤ s w by simp [rho,hu,hv]).trans hsx

end PlanarHom.MultiGraph.PlaneDrawing
