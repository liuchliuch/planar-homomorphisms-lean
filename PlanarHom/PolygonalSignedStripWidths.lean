import PlanarHom.PlanarRibbonExistence

/-!
# NEW proof: one common width for both signed normal ribbons

Reversing every directed segment converts the negative normal into a positive
normal for the existing, proved finite strip geometry. Transporting its actual
width inequalities back yields both signed ribbons on the unchanged drawing.
This module proves their individual ribbon conditions; it does not assume or
assert an exhaustive face decomposition or a Jordan theorem.
-/
noncomputable section
open Set unitInterval Filter
open scoped Topology Convex
namespace PlanarHom.Polygonal
open MultiGraph

/-- Reverse the directed finite pieces, keeping their geometric segments. -/
def reversePieces (S : Finset (Plane × Plane)) : Finset (Plane × Plane) := S.image Prod.swap

@[simp] theorem mem_reversePieces (S : Finset (Plane × Plane)) (a b : Plane) :
    (a,b) ∈ reversePieces S ↔ (b,a) ∈ S := by
  simp [reversePieces,Finset.mem_image,Prod.ext_iff,and_assoc]

/-- Reversal merely exchanges the unique incoming/outgoing corner roles. -/
theorem twoValentCorners_reverse (S : Finset (Plane × Plane)) (H : Set Plane)
    (h : TwoValentCorners (S : Set (Plane × Plane)) H) :
    TwoValentCorners (reversePieces S : Set (Plane × Plane)) H := by
  intro x hx htouch
  obtain ⟨a,b,hab,habx⟩ := htouch
  have hba : (b,a) ∈ S := (mem_reversePieces S a b).mp hab
  obtain ⟨P,Q,hPx,hxQ,hi,hs,hp⟩ := h x hx ⟨b,a,hba,habx.symm⟩
  refine ⟨Q,P,hxQ.symm,hPx.symm,?_,?_,?_⟩
  · intro z hz hz'
    exact hi z (by simpa only [segment_symm] using hz') (by simpa only [segment_symm] using hz)
  · intro c d hcd hc
    exact hp d c ((mem_reversePieces S c d).mp hcd) hc
  · intro c d hcd hd
    exact hs d c ((mem_reversePieces S c d).mp hcd) hd

theorem endpointIntersections_reverse (S : Finset (Plane × Plane))
    (h : EndpointIntersections (S : Set (Plane × Plane))) :
    EndpointIntersections (reversePieces S : Set (Plane × Plane)) := by
  rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd hne
  have hba := (mem_reversePieces S a b).mp hab
  have hdc := (mem_reversePieces S c d).mp hcd
  have hne' : (b,a) ≠ (d,c) := fun heq => hne (congrArg Prod.swap heq)
  rcases h (b,a) hba (d,c) hdc hne' with hdis | ⟨x,hl,hr,hi⟩
  · left
    simpa only [segment_symm] using hdis
  · exact Or.inr ⟨x,hl.symm,hr.symm,fun z hz hz' =>
      hi z (by simpa only [segment_symm] using hz) (by simpa only [segment_symm] using hz')⟩

/-- Reverse only the longitudinal coordinate of a strip square. -/
def reverseSquare (p : I × I) : I × I := (unitInterval.symm p.1,p.2)

@[simp] theorem reverseSquare_involutive (p : I × I) : reverseSquare (reverseSquare p) = p := by
  simp [reverseSquare]

theorem stripMap_reverseSquare (a b A B : Plane) (p : I × I) :
    stripMap b a B A (reverseSquare p) = stripMap a b A B p := by
  exact (strip_reverse a b A B p.1 p.2).symm

theorem lineMap_reverseSquare (a b : Plane) (p : I × I) :
    AffineMap.lineMap b a ((reverseSquare p).1 : ℝ) = AffineMap.lineMap a b (p.1 : ℝ) :=
  AffineMap.lineMap_apply_one_sub b a (p.1 : ℝ)

/-- Transport the complete numerical width conditions back across reversal. -/
theorem GoodStripWidth.of_reverse {S : Finset (Plane × Plane)} {H : Set Plane}
    {N : Plane → Plane} {ε : ℝ} (h : GoodStripWidth (reversePieces S) H N ε) :
    GoodStripWidth S H N ε := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨a,b⟩ hab p q heq
    have hba := (mem_reversePieces S b a).mpr hab
    have hh := h.1 (b,a) hba (reverseSquare p) (reverseSquare q)
      (by simpa only [stripMap_reverseSquare] using heq)
    rcases hh with hpq | ⟨hb,hp,hq⟩ | ⟨ha,hp,hq⟩
    · exact Or.inl (by simpa only [reverseSquare_involutive] using congrArg reverseSquare hpq)
    · right; right
      refine ⟨hb,?_,?_⟩
      · have hh := congrArg unitInterval.symm hp
        simpa [reverseSquare] using hh
      · have hh := congrArg unitInterval.symm hq
        simpa [reverseSquare] using hh
    · right; left
      refine ⟨ha,?_,?_⟩
      · have hh := congrArg unitInterval.symm hp
        simpa [reverseSquare] using hh
      · have hh := congrArg unitInterval.symm hq
        simpa [reverseSquare] using hh
  · rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd p q heq
    have hh := h.2.1 (b,a) ((mem_reversePieces S b a).mpr hab)
      (d,c) ((mem_reversePieces S d c).mpr hcd) (reverseSquare p) (reverseSquare q)
      (by simpa only [stripMap_reverseSquare] using heq)
    simpa only [lineMap_reverseSquare] using hh
  · rintro ⟨a,b⟩ hab x hx p heq
    have hh := h.2.2 (b,a) ((mem_reversePieces S b a).mpr hab) x hx (reverseSquare p)
      (by simpa only [stripMap_reverseSquare] using heq)
    simpa only [lineMap_reverseSquare] using hh

/-- Both signs of a fixed actual positive normal assignment satisfy the proved
strip requirements at every sufficiently small common positive width. -/
theorem eventually_signed_good_strip_width (S : Finset (Plane × Plane)) (H : Set Plane)
    (hH : H.Finite) (N : Plane → Plane)
    (hcorner : TwoValentCorners (S : Set (Plane × Plane)) H)
    (hpair : EndpointIntersections (S : Set (Plane × Plane)))
    (hne : ∀ e ∈ S, e.1 ≠ e.2)
    (hvertex : HostEndpointOnly (S : Set (Plane × Plane)) H)
    (hzero : ∀ x ∈ H, N x = 0)
    (hout : ∀ a b, (a,b) ∈ S → a ∉ H → 0 < cross (b-a) (N a))
    (hin : ∀ a b, (a,b) ∈ S → b ∉ H → 0 < cross (b-a) (N b))
    (hfree : ∀ a b, (a,b) ∈ S → a ∉ H ∨ b ∉ H) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0,
      GoodStripWidth S H N ε ∧ GoodStripWidth S H (fun x => -N x) ε := by
  have hrne : ∀ e ∈ reversePieces S, e.1 ≠ e.2 := by
    rintro ⟨a,b⟩ hab
    exact (hne (b,a) ((mem_reversePieces S a b).mp hab)).symm
  have hrvertex : HostEndpointOnly (reversePieces S : Set (Plane × Plane)) H := by
    rintro ⟨a,b⟩ hab x hx hseg
    exact (hvertex (b,a) ((mem_reversePieces S a b).mp hab) x hx
      (by simpa only [segment_symm] using hseg)).symm
  have hrzero : ∀ x ∈ H, -N x = 0 := by intro x hx; simp [hzero x hx]
  have hrout : ∀ a b, (a,b) ∈ reversePieces S → a ∉ H → 0 < cross (b-a) (-N a) := by
    intro a b hab ha
    have hh := hin b a ((mem_reversePieces S a b).mp hab) ha
    have hba : b-a = -(a-b) := by abel
    simpa only [hba,cross_neg_left,cross_neg_right,neg_neg] using hh
  have hrin : ∀ a b, (a,b) ∈ reversePieces S → b ∉ H → 0 < cross (b-a) (-N b) := by
    intro a b hab hb
    have hh := hout b a ((mem_reversePieces S a b).mp hab) hb
    have hba : b-a = -(a-b) := by abel
    simpa only [hba,cross_neg_left,cross_neg_right,neg_neg] using hh
  have hrfree : ∀ a b, (a,b) ∈ reversePieces S → a ∉ H ∨ b ∉ H := by
    intro a b hab
    exact (hfree b a ((mem_reversePieces S a b).mp hab)).symm
  filter_upwards [eventually_good_strip_width S H hH N hcorner hpair hne hvertex hzero hout hin hfree,
    eventually_good_strip_width (reversePieces S) H hH (fun x => -N x)
      (twoValentCorners_reverse S H hcorner) (endpointIntersections_reverse S hpair)
      hrne hrvertex hrzero hrout hrin hrfree] with ε hp hn
  exact ⟨hp,hn.of_reverse⟩

end PlanarHom.Polygonal
