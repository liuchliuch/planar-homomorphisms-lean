import PlanarHom.PlanarColoringTwoWayConverter

/-! Expanded one-way color converter, Figure 14 of Barbanchon (2004).
All three palette-copying diamonds and both two-way converters are literal
subgraphs. This module proves exact coloring semantics and unique extension;
the geometric assembly is a separate obligation. -/
noncomputable section
namespace PlanarHom.PlanarColoringOneWayConverter
open MultiGraph
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 10000

abbrev Edge := (Fin 3 × Fin 8) ⊕ (Bool × PlanarColoringTwoWayConverter.Edge)
def wheelMap : Fin 3 → Fin 5 → Fin 34 :=
  ![![0,3,8,6,11],![9,5,10,7,12],![2,4,5,3,13]]
def leftMap : Fin 14 → Fin 34 := ![8,9,5,6,14,15,16,17,18,19,20,21,22,23]
def rightMap : Fin 14 → Fin 34 := ![10,1,7,4,24,25,26,27,28,29,30,31,32,33]
def converterMap (b : Bool) : Fin 14 → Fin 34 := if b then rightMap else leftMap

def graph : MultiGraph (Fin 34) Edge where
  src := Sum.elim (fun p => wheelMap p.1 (PlanarColoringExclusiveCrossing.graph.src p.2))
    (fun p => converterMap p.1 (PlanarColoringTwoWayConverter.graph.src p.2))
  dst := Sum.elim (fun p => wheelMap p.1 (PlanarColoringExclusiveCrossing.graph.dst p.2))
    (fun p => converterMap p.1 (PlanarColoringTwoWayConverter.graph.dst p.2))

def Proper (col : Fin 34 → Fin 3) : Prop := ∀ e,col (graph.src e)≠col (graph.dst e)
def Relation (x xp : Fin 3) : Prop := x≠1 ∧ (x=2 ↔ xp=2)
instance (x xp : Fin 3) : Decidable (Relation x xp) := by unfold Relation; infer_instance
def middleColor (x : Fin 3) : Fin 3 := if x=2 then 2 else 1

theorem core_iff (x j xp : Fin 3) :
    (x≠1 ∧ j≠0 ∧ (x=2 ↔ j=2) ∧ (j=2 ↔ xp=2)) ↔ Relation x xp ∧ j=middleColor x := by
  have h : ∀ x j xp : Fin 3,
      (x≠1 ∧ j≠0 ∧ (x=2 ↔ j=2) ∧ (j=2 ↔ xp=2)) ↔ Relation x xp ∧ j=middleColor x := by
    unfold Relation middleColor
    decide
  exact h x j xp

def extension (x xp : Fin 3) : Fin 34 → Fin 3 :=
  ![x,xp,0,1,1,0,1,0,x,middleColor x,middleColor x,
    PlanarColoringExclusiveCrossing.third x 1,PlanarColoringExclusiveCrossing.third (middleColor x) 0,
    PlanarColoringExclusiveCrossing.third 0 1,
    PlanarColoringTwoWayConverter.extension x (middleColor x) 4,
    PlanarColoringTwoWayConverter.extension x (middleColor x) 5,
    PlanarColoringTwoWayConverter.extension x (middleColor x) 6,
    PlanarColoringTwoWayConverter.extension x (middleColor x) 7,
    PlanarColoringTwoWayConverter.extension x (middleColor x) 8,
    PlanarColoringTwoWayConverter.extension x (middleColor x) 9,
    PlanarColoringTwoWayConverter.extension x (middleColor x) 10,
    PlanarColoringTwoWayConverter.extension x (middleColor x) 11,
    PlanarColoringTwoWayConverter.extension x (middleColor x) 12,
    PlanarColoringTwoWayConverter.extension x (middleColor x) 13,
    PlanarColoringTwoWayConverter.extension (middleColor x) xp 4,
    PlanarColoringTwoWayConverter.extension (middleColor x) xp 5,
    PlanarColoringTwoWayConverter.extension (middleColor x) xp 6,
    PlanarColoringTwoWayConverter.extension (middleColor x) xp 7,
    PlanarColoringTwoWayConverter.extension (middleColor x) xp 8,
    PlanarColoringTwoWayConverter.extension (middleColor x) xp 9,
    PlanarColoringTwoWayConverter.extension (middleColor x) xp 10,
    PlanarColoringTwoWayConverter.extension (middleColor x) xp 11,
    PlanarColoringTwoWayConverter.extension (middleColor x) xp 12,
    PlanarColoringTwoWayConverter.extension (middleColor x) xp 13]

theorem proper_split (col : Fin 34 → Fin 3) : Proper col ↔
    (∀ k : Fin 3, PlanarColoringExclusiveCrossing.Proper (col ∘ wheelMap k)) ∧
      PlanarColoringTwoWayConverter.Proper (col ∘ leftMap) ∧
      PlanarColoringTwoWayConverter.Proper (col ∘ rightMap) := by
  constructor
  · intro h
    exact ⟨fun k e => h (.inl (k,e)),fun e => h (.inr (false,e)),fun e => h (.inr (true,e))⟩
  · rintro ⟨hw,hl,hr⟩ e
    rcases e with ⟨k,e⟩ | ⟨b,e⟩
    · exact hw k e
    · cases b
      · exact hl e
      · exact hr e

/-- Pinned palette ports determine all remaining palette copies, intermediate
values and internal gadget vertices, with exactly three allowed input/output pairs. -/
theorem proper_pinned_iff (col : Fin 34 → Fin 3) :
    Proper col ∧ col 7=0 ∧ col 6=1 ↔ Relation (col 0) (col 1) ∧ col=extension (col 0) (col 1) := by
  constructor
  · rintro ⟨hp,hb,hg⟩
    obtain ⟨hw,hl,hr⟩ := (proper_split col).mp hp
    obtain ⟨hn0,he0⟩ := (PlanarColoringExclusiveCrossing.proper_iff _).mp (hw 0)
    obtain ⟨hn1,he1⟩ := (PlanarColoringExclusiveCrossing.proper_iff _).mp (hw 1)
    obtain ⟨hn2,he2⟩ := (PlanarColoringExclusiveCrossing.proper_iff _).mp (hw 2)
    have h8 : col 8=col 0 := congrFun he0 2
    have h3 : col 3=1 := by
      have he : col 6=col 3 := congrFun he0 3
      exact he.symm.trans hg
    have h10 : col 10=col 9 := congrFun he1 2
    have h5 : col 5=0 := by
      have he : col 7=col 5 := congrFun he1 3
      exact he.symm.trans hb
    have h2 : col 2=0 := by
      have he : col 5=col 2 := congrFun he2 2
      exact he.symm.trans h5
    have h4 : col 4=1 := by
      have he : col 3=col 4 := congrFun he2 3
      exact he.symm.trans h3
    have h11 : col 11=PlanarColoringExclusiveCrossing.third (col 0) 1 := by
      have he : col 11=PlanarColoringExclusiveCrossing.third (col 0) (col 3) := congrFun he0 4
      rwa [h3] at he
    have h12 : col 12=PlanarColoringExclusiveCrossing.third (col 9) 0 := by
      have he : col 12=PlanarColoringExclusiveCrossing.third (col 9) (col 5) := congrFun he1 4
      rwa [h5] at he
    have h13 : col 13=PlanarColoringExclusiveCrossing.third 0 1 := by
      have he : col 13=PlanarColoringExclusiveCrossing.third (col 2) (col 4) := congrFun he2 4
      rwa [h2,h4] at he
    have hleft := (PlanarColoringTwoWayConverter.proper_pinned_iff (col ∘ leftMap)).mp ⟨hl,h5,hg⟩
    have hright := (PlanarColoringTwoWayConverter.proper_pinned_iff (col ∘ rightMap)).mp ⟨hr,hb,h4⟩
    change (col 8=2 ↔ col 9=2) ∧ _ at hleft
    change (col 10=2 ↔ col 1=2) ∧ _ at hright
    change col 0≠col 3 at hn0
    change col 9≠col 5 at hn1
    rw [h3] at hn0
    rw [h5] at hn1
    rw [h8] at hleft
    rw [h10] at hright
    obtain ⟨hrel,h9⟩ := (core_iff _ _ _).mp ⟨hn0,hn1,hleft.1,hright.1⟩
    have hl' : col ∘ leftMap=PlanarColoringTwoWayConverter.extension (col 0) (middleColor (col 0)) := by
      simpa only [Function.comp_apply,leftMap,Matrix.cons_val_zero,Matrix.cons_val_one,h8,h9] using hleft.2
    have hr' : col ∘ rightMap=PlanarColoringTwoWayConverter.extension (middleColor (col 0)) (col 1) := by
      simpa only [Function.comp_apply,rightMap,Matrix.cons_val_zero,Matrix.cons_val_one,h10,h9] using hright.2
    refine ⟨hrel,?_⟩
    funext v
    fin_cases v
    · rfl
    · rfl
    · dsimp [extension]
      simp only [hb,hg,h2,h3,h4,h5,h8,h10,h11,h12,h13,h9]
    · dsimp [extension]
      simp only [hb,hg,h2,h3,h4,h5,h8,h10,h11,h12,h13,h9]
    · dsimp [extension]
      simp only [hb,hg,h2,h3,h4,h5,h8,h10,h11,h12,h13,h9]
    · dsimp [extension]
      simp only [hb,hg,h2,h3,h4,h5,h8,h10,h11,h12,h13,h9]
    · dsimp [extension]
      simp only [hb,hg,h2,h3,h4,h5,h8,h10,h11,h12,h13,h9]
    · dsimp [extension]
      simp only [hb,hg,h2,h3,h4,h5,h8,h10,h11,h12,h13,h9]
    · dsimp [extension]
      simp only [hb,hg,h2,h3,h4,h5,h8,h10,h11,h12,h13,h9]
    · dsimp [extension]
      simp only [hb,hg,h2,h3,h4,h5,h8,h10,h11,h12,h13,h9]
    · dsimp [extension]
      simp only [hb,hg,h2,h3,h4,h5,h8,h10,h11,h12,h13,h9]
    · dsimp [extension]
      simp only [hb,hg,h2,h3,h4,h5,h8,h10,h11,h12,h13,h9]
    · dsimp [extension]
      simp only [hb,hg,h2,h3,h4,h5,h8,h10,h11,h12,h13,h9]
    · dsimp [extension]
      simp only [hb,hg,h2,h3,h4,h5,h8,h10,h11,h12,h13,h9]
    · exact congrFun hl' 4
    · exact congrFun hl' 5
    · exact congrFun hl' 6
    · exact congrFun hl' 7
    · exact congrFun hl' 8
    · exact congrFun hl' 9
    · exact congrFun hl' 10
    · exact congrFun hl' 11
    · exact congrFun hl' 12
    · exact congrFun hl' 13
    · exact congrFun hr' 4
    · exact congrFun hr' 5
    · exact congrFun hr' 6
    · exact congrFun hr' 7
    · exact congrFun hr' 8
    · exact congrFun hr' 9
    · exact congrFun hr' 10
    · exact congrFun hr' 11
    · exact congrFun hr' 12
    · exact congrFun hr' 13
  · rintro ⟨hrel,he⟩
    have hcore := (core_iff (col 0) (middleColor (col 0)) (col 1)).mpr ⟨hrel,rfl⟩
    rcases hcore with ⟨hx,hj,hl,hr⟩
    have hw (k : Fin 3) : PlanarColoringExclusiveCrossing.Proper (extension (col 0) (col 1) ∘ wheelMap k) := by
      fin_cases k
      · change PlanarColoringExclusiveCrossing.Proper (extension (col 0) (col 1) ∘ wheelMap 0)
        have heq : extension (col 0) (col 1) ∘ wheelMap 0=PlanarColoringExclusiveCrossing.extension (col 0) 1 := by
          funext i; fin_cases i <;> rfl
        rw [heq]
        exact PlanarColoringExclusiveCrossing.extension_proper _ _ hx
      · change PlanarColoringExclusiveCrossing.Proper (extension (col 0) (col 1) ∘ wheelMap 1)
        have heq : extension (col 0) (col 1) ∘ wheelMap 1=PlanarColoringExclusiveCrossing.extension (middleColor (col 0)) 0 := by
          funext i; fin_cases i <;> rfl
        rw [heq]
        exact PlanarColoringExclusiveCrossing.extension_proper _ _ hj
      · change PlanarColoringExclusiveCrossing.Proper (extension (col 0) (col 1) ∘ wheelMap 2)
        have heq : extension (col 0) (col 1) ∘ wheelMap 2=PlanarColoringExclusiveCrossing.extension 0 1 := by
          funext i; fin_cases i <;> rfl
        rw [heq]
        exact PlanarColoringExclusiveCrossing.extension_proper _ _ (by decide)
    have hcL : PlanarColoringTwoWayConverter.Proper (extension (col 0) (col 1) ∘ leftMap) := by
      have heq : extension (col 0) (col 1) ∘ leftMap=PlanarColoringTwoWayConverter.extension (col 0) (middleColor (col 0)) := by
        funext i; fin_cases i <;> rfl
      rw [heq]
      exact ((PlanarColoringTwoWayConverter.proper_pinned_iff _).mpr ⟨hl,rfl⟩).1
    have hcR : PlanarColoringTwoWayConverter.Proper (extension (col 0) (col 1) ∘ rightMap) := by
      have heq : extension (col 0) (col 1) ∘ rightMap=PlanarColoringTwoWayConverter.extension (middleColor (col 0)) (col 1) := by
        funext i; fin_cases i <;> rfl
      rw [heq]
      exact ((PlanarColoringTwoWayConverter.proper_pinned_iff _).mpr ⟨hr,rfl⟩).1
    rw [he]
    exact ⟨(proper_split _).mpr ⟨hw,hcL,hcR⟩,rfl,rfl⟩

end PlanarHom.PlanarColoringOneWayConverter
