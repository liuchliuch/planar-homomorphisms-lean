import PlanarHom.IntegerStraightDrawing

/-! A kernel-checkable spatial hierarchy for large fixed integer drawings.
Bounding boxes discharge distant pairs once; only intersecting leaf boxes use
the original exact orientation checks. Nothing from an external layout solver
is trusted: coverage, bounds, leaf tests, and every recursive split are checked.
-/
noncomputable section
open Set unitInterval
namespace PlanarHom.IntegerDrawingSpatialCertificate
open MultiGraph IntegerStraightDrawing

structure Box where
  xlo : ℤ
  xhi : ℤ
  ylo : ℤ
  yhi : ℤ
  deriving DecidableEq, Repr

def Box.contains (b : Box) (p : Point) : Prop :=
  b.xlo≤p.1 ∧ p.1≤b.xhi ∧ b.ylo≤p.2 ∧ p.2≤b.yhi
instance (b : Box) (p : Point) : Decidable (b.contains p) := by unfold Box.contains; infer_instance

def Box.region (b : Box) : Set Plane := {p |
  (b.xlo:ℝ)≤p.1 ∧ p.1≤b.xhi ∧ (b.ylo:ℝ)≤p.2 ∧ p.2≤b.yhi}

def Box.sub (a b : Box) : Prop := b.xlo≤a.xlo ∧ a.xhi≤b.xhi ∧ b.ylo≤a.ylo ∧ a.yhi≤b.yhi
instance (a b : Box) : Decidable (a.sub b) := by unfold Box.sub; infer_instance

def Box.apart (a b : Box) : Prop := a.xhi<b.xlo ∨ b.xhi<a.xlo ∨ a.yhi<b.ylo ∨ b.yhi<a.ylo
instance (a b : Box) : Decidable (a.apart b) := by unfold Box.apart; infer_instance

theorem Box.contains_cast (b : Box) (p : Point) (h : b.contains p) : toPlane p∈b.region := by
  dsimp [Box.contains] at h
  change (b.xlo:ℝ)≤p.1 ∧ (p.1:ℝ)≤b.xhi ∧ (b.ylo:ℝ)≤p.2 ∧ (p.2:ℝ)≤b.yhi
  exact_mod_cast h

theorem Box.sub_region {a b : Box} (h : a.sub b) : a.region⊆b.region := by
  intro p hp
  have h' : (b.xlo:ℝ)≤a.xlo ∧ (a.xhi:ℝ)≤b.xhi ∧ (b.ylo:ℝ)≤a.ylo ∧ (a.yhi:ℝ)≤b.yhi := by exact_mod_cast h
  exact ⟨h'.1.trans hp.1,hp.2.1.trans h'.2.1,h'.2.2.1.trans hp.2.2.1,hp.2.2.2.trans h'.2.2.2⟩

theorem Box.apart_regions {a b : Box} (h : a.apart b) : Disjoint a.region b.region := by
  apply Set.disjoint_left.mpr
  intro p ha hb
  rcases h with h | h | h | h
  · have h' : (a.xhi:ℝ)<b.xlo := by exact_mod_cast h
    linarith [ha.2.1,hb.1]
  · have h' : (b.xhi:ℝ)<a.xlo := by exact_mod_cast h
    linarith [hb.2.1,ha.1]
  · have h' : (a.yhi:ℝ)<b.ylo := by exact_mod_cast h
    linarith [ha.2.2.2,hb.2.2.1]
  · have h' : (b.yhi:ℝ)<a.ylo := by exact_mod_cast h
    linarith [hb.2.2.2,ha.2.2.1]

inductive Tree (α : Type)
  | leaf : Box → α → Tree α
  | node : Box → Tree α → Tree α → Tree α
  deriving Repr

namespace Tree
variable {α β : Type}
def box : Tree α → Box
  | .leaf b _ => b
  | .node b _ _ => b

def map (f : α → β) : Tree α → Tree β
  | .leaf b a => .leaf b (f a)
  | .node b l r => .node b (map f l) (map f r)

def Mem (a : α) : Tree α → Prop
  | .leaf _ x => a=x
  | .node _ l r => Mem a l ∨ Mem a r

def lookup : Tree α → List Bool → Option α
  | .leaf _ a,[] => some a
  | .node _ l _,false::p => lookup l p
  | .node _ _ r,true::p => lookup r p
  | _,_ => none

theorem mem_of_lookup (t : Tree α) (p : List Bool) (a : α) (h : lookup t p=some a) : Mem a t := by
  induction t generalizing p with
  | leaf b x =>
    cases p
    · exact (Option.some.inj h).symm
    · simp [lookup] at h
  | node b l r ihl ihr =>
    cases p with
    | nil => simp [lookup] at h
    | cons q p =>
      cases q
      · exact Or.inl (ihl p h)
      · exact Or.inr (ihr p h)

def bounds (check : Box → α → Bool) : Tree α → Bool
  | .leaf b a => check b a
  | .node b l r => decide (l.box.sub b) && decide (r.box.sub b) && bounds check l && bounds check r

theorem bounds_sound (S : α → Set Plane) (check : Box → α → Bool)
    (leaf_sound : ∀ b a,check b a=true → S a⊆b.region) (t : Tree α) (h : bounds check t=true) :
    ∀ a,Mem a t → S a⊆t.box.region := by
  induction t with
  | leaf b x =>
    intro a ha
    subst a
    exact leaf_sound b x h
  | node b l r ihl ihr =>
    simp only [bounds,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨hl,hr⟩,hbl⟩,hbr⟩
    intro a ha
    rcases ha with ha | ha
    · exact (ihl hbl a ha).trans (Box.sub_region hl)
    · exact (ihr hbr a ha).trans (Box.sub_region hr)

def Enclosed (S : α → Set Plane) : Tree α → Prop
  | .leaf b a => S a⊆b.region
  | .node b l r => Enclosed S l ∧ Enclosed S r ∧ l.box.sub b ∧ r.box.sub b

theorem enclosed_of_bounds (S : α → Set Plane) (check : Box → α → Bool)
    (leaf_sound : ∀ b a,check b a=true → S a⊆b.region) (t : Tree α) (h : bounds check t=true) :
    Enclosed S t := by
  induction t with
  | leaf b a => exact leaf_sound b a h
  | node b l r ihl ihr =>
    simp only [bounds,Bool.and_eq_true,decide_eq_true_eq] at h
    exact ⟨ihl h.1.2,ihr h.2,h.1.1.1,h.1.1.2⟩

theorem Enclosed.mem {S : α → Set Plane} {t : Tree α} (h : Enclosed S t) :
    ∀ a,Mem a t → S a⊆t.box.region := by
  induction t with
  | leaf b x => intro a ha; subst a; exact h
  | node b l r ihl ihr =>
    intro a ha
    rcases ha with ha | ha
    · exact (ihl h.1 a ha).trans (Box.sub_region h.2.2.1)
    · exact (ihr h.2.1 a ha).trans (Box.sub_region h.2.2.2)

def apartLeaf (check : α → β → Bool) (b : Box) (a : α) : Tree β → Bool
  | .leaf c x => decide (b.apart c) || check a x
  | .node c l r => decide (b.apart c) || (apartLeaf check b a l && apartLeaf check b a r)

def apart (check : α → β → Bool) : Tree α → Tree β → Bool
  | .leaf b a,u => apartLeaf check b a u
  | .node b l r,u => decide (b.apart u.box) || (apart check l u && apart check r u)

def selfApart (check : α → α → Bool) : Tree α → Bool
  | .leaf _ _ => true
  | .node _ l r => selfApart check l && selfApart check r && apart check l r

theorem apart_node {check : α → β → Bool} {b : Box} {l r : Tree α} {u : Tree β}
    (hl : apart check l u=true) (hr : apart check r u=true) :
    apart check (.node b l r) u=true := by simp only [apart,hl,hr,Bool.true_and,Bool.or_true]

theorem apart_leaf_node {check : α → β → Bool} {b c : Box} {a : α} {l r : Tree β}
    (hl : apart check (.leaf b a) l=true) (hr : apart check (.leaf b a) r=true) :
    apart check (.leaf b a) (.node c l r)=true := by
  change apartLeaf check b a l=true at hl
  change apartLeaf check b a r=true at hr
  simp only [apart,apartLeaf,hl,hr,Bool.true_and,Bool.or_true]

theorem selfApart_node {check : α → α → Bool} {b : Box} {l r : Tree α}
    (hl : selfApart check l=true) (hr : selfApart check r=true) (ha : apart check l r=true) :
    selfApart check (.node b l r)=true := by simp only [selfApart,hl,hr,ha,Bool.true_and]

theorem apartLeaf_sound (S : α → Set Plane) (T : β → Set Plane) (check : α → β → Bool)
    (leaf_sound : ∀ a b,check a b=true → Disjoint (S a) (T b))
    (b : Box) (a : α) (hb : S a⊆b.region) (u : Tree β)
    (hu : Enclosed T u) (h : apartLeaf check b a u=true) :
    ∀ x,Mem x u → Disjoint (S a) (T x) := by
  induction u with
  | leaf c x =>
    intro y hy
    subst y
    simp only [apartLeaf,Bool.or_eq_true,decide_eq_true_eq] at h
    rcases h with h | h
    · exact (Box.apart_regions h).mono hb (hu.mem x rfl)
    · exact leaf_sound a x h
  | node c l r ihl ihr =>
    intro x hx
    simp only [apartLeaf,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with h | ⟨hl,hr⟩
    · exact (Box.apart_regions h).mono hb (hu.mem x hx)
    · rcases hx with hx | hx
      · exact ihl hu.1 hl x hx
      · exact ihr hu.2.1 hr x hx

theorem apart_sound (S : α → Set Plane) (T : β → Set Plane) (check : α → β → Bool)
    (leaf_sound : ∀ a b,check a b=true → Disjoint (S a) (T b))
    (t : Tree α) (u : Tree β) (ht : Enclosed S t) (hu : Enclosed T u)
    (h : apart check t u=true) :
    ∀ a,Mem a t → ∀ b,Mem b u → Disjoint (S a) (T b) := by
  induction t with
  | leaf box x =>
    intro a ha
    subst a
    exact apartLeaf_sound S T check leaf_sound box x ht u hu h
  | node box l r ihl ihr =>
    intro a ha b hb
    simp only [apart,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with h | ⟨hl,hr⟩
    · exact (Box.apart_regions h).mono (ht.mem a ha) (hu.mem b hb)
    · rcases ha with ha | ha
      · exact ihl ht.1 hl a ha b hb
      · exact ihr ht.2.1 hr a ha b hb

theorem selfApart_sound (S : α → Set Plane) (check : α → α → Bool)
    (leaf_sound : ∀ a b,check a b=true → Disjoint (S a) (S b))
    (t : Tree α) (ht : Enclosed S t) (h : selfApart check t=true) :
    ∀ a,Mem a t → ∀ b,Mem b t → a≠b → Disjoint (S a) (S b) := by
  induction t with
  | leaf box x =>
    intro a ha b hb hne
    exact False.elim (hne (ha.trans hb.symm))
  | node box l r ihl ihr =>
    intro a ha b hb hne
    simp only [selfApart,Bool.and_eq_true] at h
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact ihl ht.1 h.1.1 a ha b hb hne
    · exact apart_sound S S check leaf_sound l r ht.1 ht.2.1 h.2 a ha b hb
    · exact (apart_sound S S check leaf_sound l r ht.1 ht.2.1 h.2 b hb a ha).symm
    · exact ihr ht.2.1 h.1.2 a ha b hb hne

end Tree
variable {V E : Type}

def edgeSet (G : MultiGraph V E) (point : V → Point) (e : E) : Set Plane :=
  {p | ∃ t : I,Inside t ∧ affine (toPlane (point (G.src e))) (toPlane (point (G.dst e))) t=p}
def vertexSet (point : V → Point) (v : V) : Set Plane := {toPlane (point v)}

def edgeBoundCheck (G : MultiGraph V E) (point : V → Point) (b : Box) (e : E) : Bool :=
  decide (b.contains (point (G.src e))) && decide (b.contains (point (G.dst e)))
def vertexBoundCheck (point : V → Point) (b : Box) (v : V) : Bool := decide (b.contains (point v))
def edgePairCheck (G : MultiGraph V E) (point : V → Point) (e f : E) : Bool :=
  decide (Separated (point (G.src e)) (point (G.dst e)) (point (G.src f)) (point (G.dst f)))
def edgeVertexCheck (G : MultiGraph V E) (point : V → Point) (e : E) (v : V) : Bool :=
  decide (Avoids (point (G.src e)) (point (G.dst e)) (point v))

theorem affine_in_box (b : Box) (a c : Point) (ha : b.contains a) (hc : b.contains c)
    (t : I) : affine (toPlane a) (toPlane c) t∈b.region := by
  have ha' := b.contains_cast a ha
  have hc' := b.contains_cast c hc
  have ht0 := t.property.1
  have ht1 := t.property.2
  rcases ha' with ⟨hax0,hax1,hay0,hay1⟩
  rcases hc' with ⟨hcx0,hcx1,hcy0,hcy1⟩
  change (b.xlo:ℝ)≤(1-(t:ℝ))*a.1+(t:ℝ)*c.1 ∧
    (1-(t:ℝ))*a.1+(t:ℝ)*c.1≤b.xhi ∧
    (b.ylo:ℝ)≤(1-(t:ℝ))*a.2+(t:ℝ)*c.2 ∧
    (1-(t:ℝ))*a.2+(t:ℝ)*c.2≤b.yhi
  dsimp [toPlane] at hax0 hax1 hay0 hay1 hcx0 hcx1 hcy0 hcy1
  constructor
  · nlinarith [mul_nonneg (show 0≤1-(t:ℝ) by linarith) (sub_nonneg.mpr hax0),mul_nonneg ht0 (sub_nonneg.mpr hcx0)]
  constructor
  · nlinarith [mul_nonneg (show 0≤1-(t:ℝ) by linarith) (sub_nonneg.mpr hax1),mul_nonneg ht0 (sub_nonneg.mpr hcx1)]
  constructor
  · nlinarith [mul_nonneg (show 0≤1-(t:ℝ) by linarith) (sub_nonneg.mpr hay0),mul_nonneg ht0 (sub_nonneg.mpr hcy0)]
  · nlinarith [mul_nonneg (show 0≤1-(t:ℝ) by linarith) (sub_nonneg.mpr hay1),mul_nonneg ht0 (sub_nonneg.mpr hcy1)]

theorem edgeBoundCheck_sound (G : MultiGraph V E) (point : V → Point) (b : Box) (e : E)
    (h : edgeBoundCheck G point b e=true) : edgeSet G point e⊆b.region := by
  simp only [edgeBoundCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  rintro p ⟨t,_,rfl⟩
  exact affine_in_box b _ _ h.1 h.2 t

theorem vertexBoundCheck_sound (point : V → Point) (b : Box) (v : V)
    (h : vertexBoundCheck point b v=true) : vertexSet point v⊆b.region := by
  have hh : b.contains (point v) := of_decide_eq_true h
  intro p hp
  rcases hp with rfl
  exact b.contains_cast (point v) hh

theorem edgePairCheck_sound (G : MultiGraph V E) (point : V → Point) (e f : E)
    (h : edgePairCheck G point e f=true) : Disjoint (edgeSet G point e) (edgeSet G point f) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨s,hs,he⟩ ⟨t,ht,hf⟩
  exact separated_ne _ _ _ _ _ _ hs.1 hs.2 ht.1 ht.2 (of_decide_eq_true h) (he.trans hf.symm)

theorem edgeVertexCheck_sound (G : MultiGraph V E) (point : V → Point) (e : E) (v : V)
    (h : edgeVertexCheck G point e v=true) : Disjoint (edgeSet G point e) (vertexSet point v) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨s,hs,he⟩ hp
  change p=toPlane (point v) at hp
  exact avoids_ne _ _ _ _ hs.1 hs.2 (of_decide_eq_true h) (he.trans hp)

/-- Every field is checkable directly from finite explicit data. Coverage is
proved with logarithmic lookup paths, not an unchecked external permutation. -/
structure Certificate (G : MultiGraph V E) (point : V → Point) where
  injective : Function.Injective point
  nondegenerate : ∀ e,point (G.src e)≠point (G.dst e)
  edges : Tree E
  vertices : Tree V
  edgePath : E → List Bool
  vertexPath : V → List Bool
  edgeLookup : ∀ e,edges.lookup (edgePath e)=some e
  vertexLookup : ∀ v,vertices.lookup (vertexPath v)=some v
  edgeBounds : edges.bounds (edgeBoundCheck G point)=true
  vertexBounds : vertices.bounds (vertexBoundCheck point)=true
  separated : edges.selfApart (edgePairCheck G point)=true
  avoids : edges.apart (edgeVertexCheck G point) vertices=true

namespace Certificate
variable {G : MultiGraph V E} {point : V → Point} (h : Certificate G point)

theorem edge_enclosed : h.edges.Enclosed (edgeSet G point) :=
  Tree.enclosed_of_bounds (edgeSet G point) (edgeBoundCheck G point)
    (edgeBoundCheck_sound G point) h.edges h.edgeBounds

theorem vertex_enclosed : h.vertices.Enclosed (vertexSet point) :=
  Tree.enclosed_of_bounds (vertexSet point) (vertexBoundCheck point)
    (vertexBoundCheck_sound point) h.vertices h.vertexBounds

theorem edge_mem (e : E) : h.edges.Mem e := Tree.mem_of_lookup _ _ _ (h.edgeLookup e)
theorem vertex_mem (v : V) : h.vertices.Mem v := Tree.mem_of_lookup _ _ _ (h.vertexLookup v)

include h in
theorem edges_disjoint (e f : E) (hef : e≠f) : Disjoint (edgeSet G point e) (edgeSet G point f) :=
  Tree.selfApart_sound (edgeSet G point) (edgePairCheck G point) (edgePairCheck_sound G point)
    h.edges h.edge_enclosed h.separated e (h.edge_mem e) f (h.edge_mem f) hef

include h in
theorem edge_vertex_disjoint (e : E) (v : V) : Disjoint (edgeSet G point e) (vertexSet point v) :=
  Tree.apart_sound (edgeSet G point) (vertexSet point) (edgeVertexCheck G point)
    (edgeVertexCheck_sound G point) h.edges h.vertices h.edge_enclosed h.vertex_enclosed
    h.avoids e (h.edge_mem e) v (h.vertex_mem v)

private theorem affine_parameter_injective (a b : Plane) (hab : a≠b) {s t : ℝ}
    (h : affine a b s=affine a b t) : s=t := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [affine] at hx hy
  by_cases he : a.1=b.1
  · have hn : a.2≠b.2 := by intro he'; exact hab (Prod.ext he he')
    have hp : (s-t)*(b.2-a.2)=0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr hn.symm))
  · have hp : (s-t)*(b.1-a.1)=0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr (Ne.symm he)))

/-- Actual continuous, injective, mutually noncrossing edge curves certified by
the recursively checked finite spatial data. -/
def drawing : PlaneDrawing G where
  point := toPlane ∘ point
  point_injective := by
    intro v w he
    apply h.injective
    apply Prod.ext
    · have hh := congrArg Prod.fst he
      dsimp [toPlane] at hh
      exact_mod_cast hh
    · have hh := congrArg Prod.snd he
      dsimp [toPlane] at hh
      exact_mod_cast hh
  curve := IntegerStraightDrawing.curve G point
  curve_zero e := by simp [IntegerStraightDrawing.curve,affine]
  curve_one e := by simp [IntegerStraightDrawing.curve,affine]
  interior_injective := by
    intro e f s t hs ht he
    by_cases hef : e=f
    · subst f
      refine ⟨rfl,Subtype.ext ?_⟩
      apply affine_parameter_injective _ _ _ he
      intro hp
      apply h.nondegenerate e
      apply Prod.ext
      · have hx := congrArg Prod.fst hp; dsimp [toPlane] at hx; exact_mod_cast hx
      · have hy := congrArg Prod.snd hp; dsimp [toPlane] at hy; exact_mod_cast hy
    · exact False.elim (Set.disjoint_left.mp (h.edges_disjoint e f hef)
        ⟨s,hs,rfl⟩ ⟨t,ht,he.symm⟩)
  interior_avoids := by
    intro e t ht v he
    exact Set.disjoint_left.mp (h.edge_vertex_disjoint e v) ⟨t,ht,rfl⟩ he

end Certificate
end PlanarHom.IntegerDrawingSpatialCertificate
