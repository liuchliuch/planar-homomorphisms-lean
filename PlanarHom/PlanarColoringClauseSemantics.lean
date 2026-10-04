import PlanarHom.PlanarColoringClauseGraph

/-! Exact positive-one-in-three semantics of the literal palette-linked clause
graph. Every input and every internal coloring value is reconstructed uniquely. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarColoringClause
open ParsimoniousNorOneInThree
set_option maxHeartbeats 8000000
set_option maxRecDepth 6000
set_option synthInstance.maxSize 20000

def boolColor (b : Bool) : Fin 3 := if b then 2 else 0

def coreColors (b : Fin 3 → Bool) : Fin 3 → Fin 3 :=
  ![if b 0 then 2 else 0,if b 0 then 0 else if b 1 then 2 else 1,if b 2 then 2 else 1]

def Core (x y z i j k : Fin 3) : Prop :=
  PlanarColoringOneWayConverter.Relation x i ∧ PlanarColoringOneWayConverter.Relation y j ∧
  PlanarColoringOneWayConverter.Relation z k ∧ i≠j ∧ j≠k ∧ k≠i ∧ i≠1 ∧ k≠0

theorem core_iff (x y z i j k : Fin 3) :
    Core x y z i j k ↔ ExactlyOne (decide (x=2)) (decide (y=2)) (decide (z=2)) ∧
      x=boolColor (decide (x=2)) ∧ y=boolColor (decide (y=2)) ∧ z=boolColor (decide (z=2)) ∧
      i=coreColors ![decide (x=2),decide (y=2),decide (z=2)] 0 ∧
      j=coreColors ![decide (x=2),decide (y=2),decide (z=2)] 1 ∧
      k=coreColors ![decide (x=2),decide (y=2),decide (z=2)] 2 := by
  have h : ∀ x y z i j k : Fin 3,
      Core x y z i j k ↔ ExactlyOne (decide (x=2)) (decide (y=2)) (decide (z=2)) ∧
        x=boolColor (decide (x=2)) ∧ y=boolColor (decide (y=2)) ∧ z=boolColor (decide (z=2)) ∧
        i=coreColors ![decide (x=2),decide (y=2),decide (z=2)] 0 ∧
        j=coreColors ![decide (x=2),decide (y=2),decide (z=2)] 1 ∧
        k=coreColors ![decide (x=2),decide (y=2),decide (z=2)] 2 := by
    unfold Core PlanarColoringOneWayConverter.Relation ExactlyOne boolColor coreColors
    decide
  exact h x y z i j k

def inputBits (col : Vertex → Fin 3) : Fin 3 → Bool := fun k => decide (col (copyVertex k 0)=2)

def extension (b : Fin 3 → Bool) (v : Vertex) : Fin 3 :=
  if h : v.val<102 then
    PlanarColoringOneWayConverter.extension (boolColor (b ⟨v.val/34,by omega⟩))
      (coreColors b ⟨v.val/34,by omega⟩) ⟨v.val%34,by omega⟩
  else 2

@[simp] theorem extension_copy (b : Fin 3 → Bool) (k : Fin 3) (v : Fin 34) :
    extension b (copyVertex k v)=PlanarColoringOneWayConverter.extension (boolColor (b k)) (coreColors b k) v := by
  have hlt : 34*k.val+v.val<102 := by omega
  have hdiv : (34*k.val+v.val)/34=k.val := by omega
  have hmod : (34*k.val+v.val)%34=v.val := by omega
  simp [extension,copyVertex,hlt,hdiv,hmod]

@[simp] theorem extension_center (b : Fin 3 → Bool) (k : Fin 3) : extension b (centerVertex k)=2 := by
  simp [extension,centerVertex]

theorem vertex_cases (v : Vertex) : (∃ k w,v=copyVertex k w) ∨ ∃ k,v=centerVertex k := by
  by_cases hv : v.val<102
  · left
    refine ⟨⟨v.val/34,by omega⟩,⟨v.val%34,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [copyVertex]
    omega
  · right
    refine ⟨⟨v.val-102,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [centerVertex]
    omega

/-- Reference colors propagate around the three actual palette-link diamonds. -/
theorem palettes_pinned (col : Vertex → Fin 3) (hp : Proper col)
    (hb : col (copyVertex 0 7)=0) (hg : col (copyVertex 0 6)=1) :
    ∀ k,col (copyVertex k 7)=0 ∧ col (copyVertex k 6)=1 := by
  have hs := (proper_split col).mp hp
  have hnext (k : Fin 3) (hk : col (copyVertex k 7)=0 ∧ col (copyVertex k 6)=1) :
      col (copyVertex (next k) 7)=0 ∧ col (copyVertex (next k) 6)=1 := by
    have hc := PlanarColoringOneWayConverter.palette_copy (col ∘ copyVertex k) (hs.1 k)
    have hw := (PlanarColoringExclusiveCrossing.proper_iff _).mp (hs.2.1 k)
    have hh0 : col (copyVertex (next k) 7)=col (copyVertex k 2) := congrFun hw.2 2
    have hh1 : col (copyVertex (next k) 6)=col (copyVertex k 4) := congrFun hw.2 3
    exact ⟨hh0.trans (hc.1.trans hk.1),hh1.trans (hc.2.1.trans hk.2)⟩
  have h0 := And.intro hb hg
  have h1 := hnext 0 h0
  have h2 := hnext 1 h1
  intro k
  fin_cases k <;> first | exact h0 | exact h1 | exact h2

/-- Forward unique reconstruction from the graph's actual coloring constraints. -/
theorem reconstruct (col : Vertex → Fin 3) (hp : Proper col)
    (hb : col (copyVertex 0 7)=0) (hg : col (copyVertex 0 6)=1) :
    ExactlyOne (inputBits col 0) (inputBits col 1) (inputBits col 2) ∧ col=extension (inputBits col) := by
  have hs := (proper_split col).mp hp
  have hpal := palettes_pinned col hp hb hg
  have hcomp (k : Fin 3) := (PlanarColoringOneWayConverter.proper_pinned_iff (col ∘ copyVertex k)).mp
    ⟨hs.1 k,(hpal k).1,(hpal k).2⟩
  have h4 : col (copyVertex 0 4)=1 :=
    (PlanarColoringOneWayConverter.palette_copy (col ∘ copyVertex 0) (hs.1 0)).2.1.trans hg
  have hcore : Core (col (copyVertex 0 0)) (col (copyVertex 1 0)) (col (copyVertex 2 0))
      (col (copyVertex 0 1)) (col (copyVertex 1 1)) (col (copyVertex 2 1)) := by
    rcases hs.2.2 with ⟨h01,h12,h20,hi,hk⟩
    rw [h4] at hi
    rw [(hpal 2).1] at hk
    exact ⟨(hcomp 0).1,(hcomp 1).1,(hcomp 2).1,h01,h12,h20,hi,hk⟩
  have h := (core_iff _ _ _ _ _ _).mp hcore
  have hin : ∀ k,col (copyVertex k 0)=boolColor (inputBits col k) := by
    intro k
    fin_cases k <;> first | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2.1
  have hout : ∀ k,col (copyVertex k 1)=coreColors (inputBits col) k := by
    intro k
    fin_cases k <;> first | exact h.2.2.2.2.1 | exact h.2.2.2.2.2.1 | exact h.2.2.2.2.2.2
  refine ⟨h.1,?_⟩
  funext v
  rcases vertex_cases v with ⟨k,w,rfl⟩ | ⟨k,rfl⟩
  · rw [extension_copy]
    have he := congrFun (hcomp k).2 w
    change col (copyVertex k w)=PlanarColoringOneWayConverter.extension (col (copyVertex k 0)) (col (copyVertex k 1)) w at he
    rwa [hin k,hout k] at he
  · rw [extension_center]
    have hw := (PlanarColoringExclusiveCrossing.proper_iff _).mp (hs.2.1 k)
    have hc := PlanarColoringOneWayConverter.palette_copy (col ∘ copyVertex k) (hs.1 k)
    have he : col (centerVertex k)=PlanarColoringExclusiveCrossing.third (col (copyVertex k 2)) (col (copyVertex k 4)) :=
      congrFun hw.2 4
    have hb' : col (copyVertex k 2)=0 := hc.1.trans (hpal k).1
    have hg' : col (copyVertex k 4)=1 := hc.2.1.trans (hpal k).2
    rw [hb',hg'] at he
    exact he


theorem inputBits_extension (b : Fin 3 → Bool) : inputBits (extension b)=b := by
  funext k
  simp only [inputBits,extension_copy]
  change decide (boolColor (b k)=2)=b k
  cases b k <;> rfl

theorem core_extension (b : Fin 3 → Bool) (hb : ExactlyOne (b 0) (b 1) (b 2)) :
    Core (boolColor (b 0)) (boolColor (b 1)) (boolColor (b 2))
      (coreColors b 0) (coreColors b 1) (coreColors b 2) := by
  cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;>
    simp [ExactlyOne,Core,PlanarColoringOneWayConverter.Relation,boolColor,coreColors,h0,h1,h2,
      Matrix.cons_val_two] at hb ⊢

/-- Every satisfying Boolean triple extends to a coloring of this exact graph. -/
theorem extension_proper (b : Fin 3 → Bool) (hb : ExactlyOne (b 0) (b 1) (b 2)) : Proper (extension b) := by
  obtain ⟨hr0,hr1,hr2,h01,h12,h20,hi,hk⟩ := core_extension b hb
  have hc (k : Fin 3) : PlanarColoringOneWayConverter.Proper (extension b ∘ copyVertex k) := by
    have he : extension b ∘ copyVertex k=PlanarColoringOneWayConverter.extension (boolColor (b k)) (coreColors b k) := by
      funext v
      exact extension_copy b k v
    rw [he]
    apply ((PlanarColoringOneWayConverter.proper_pinned_iff _).mpr ⟨?_,rfl⟩).1
    fin_cases k <;> first | exact hr0 | exact hr1 | exact hr2
  have hg (k : Fin 3) : PlanarColoringExclusiveCrossing.Proper (extension b ∘ gapMap k) := by
    have he : extension b ∘ gapMap k=PlanarColoringExclusiveCrossing.extension 0 1 := by
      funext v
      fin_cases v <;> dsimp [gapMap,PlanarColoringExclusiveCrossing.extension]
      all_goals first | (rw [extension_copy]; rfl) | exact extension_center b k
    rw [he]
    exact PlanarColoringExclusiveCrossing.extension_proper _ _ (by decide)
  apply (proper_split _).mpr
  refine ⟨hc,hg,?_,?_,?_,?_,?_⟩
  · simpa only [extension_copy] using h01
  · simpa only [extension_copy] using h12
  · simpa only [extension_copy] using h20
  · simpa only [extension_copy] using hi
  · simpa only [extension_copy] using hk

/-- Full iff, including all auxiliary and palette-copy vertices. -/
theorem proper_pinned_iff (col : Vertex → Fin 3) :
    Proper col ∧ col (copyVertex 0 7)=0 ∧ col (copyVertex 0 6)=1 ↔
      ExactlyOne (inputBits col 0) (inputBits col 1) (inputBits col 2) ∧ col=extension (inputBits col) := by
  constructor
  · rintro ⟨hp,hb,hg⟩
    exact reconstruct col hp hb hg
  · rintro ⟨hb,he⟩
    rw [he]
    exact ⟨extension_proper _ hb,by rw [extension_copy]; rfl,by rw [extension_copy]; rfl⟩

end PlanarHom.PlanarColoringClause
