import PlanarHom.PlanarColoringExclusiveCrossing

/-! Literal parsimonious two-way color converter, expanded from Figure 13 of
Barbanchon (2004). Its two exclusive diamonds are the actual five-vertex wheel
proved previously. Black=0, gray=1, white=2; palettes are pinned explicitly. -/
noncomputable section
namespace PlanarHom.PlanarColoringTwoWayConverter
open MultiGraph
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 10000

abbrev Edge := Fin 8 ⊕ (Fin 8 ⊕ Fin 10)
def topMap : Fin 5 → Fin 14 := ![10,4,2,5,12]
def bottomMap : Fin 5 → Fin 14 := ![3,8,11,7,13]
def extraSrc : Fin 10 → Fin 14 := ![0,0,10,6,6,5,8,9,7,5]
def extraDst : Fin 10 → Fin 14 := ![4,8,6,5,8,9,9,11,1,1]

def graph : MultiGraph (Fin 14) Edge where
  src := Sum.elim (topMap ∘ PlanarColoringExclusiveCrossing.graph.src) (Sum.elim (bottomMap ∘ PlanarColoringExclusiveCrossing.graph.src) extraSrc)
  dst := Sum.elim (topMap ∘ PlanarColoringExclusiveCrossing.graph.dst) (Sum.elim (bottomMap ∘ PlanarColoringExclusiveCrossing.graph.dst) extraDst)

def Proper (col : Fin 14 → Fin 3) : Prop := ∀ e,col (graph.src e)≠col (graph.dst e)

def Core (x xp i ip k kp : Fin 3) : Prop :=
  i≠0 ∧ ip≠1 ∧ x≠i ∧ x≠ip ∧ 0≠k ∧ k≠i ∧ k≠ip ∧ i≠kp ∧ ip≠kp ∧ kp≠1 ∧ ip≠xp ∧ i≠xp

def colors (x : Fin 3) : Fin 4 → Fin 3 :=
  if x=2 then ![1,0,2,2] else ![2,2,1,0]

/-- Complete finite local analysis, including every auxiliary value. -/
theorem core_iff (x xp i ip k kp : Fin 3) :
    Core x xp i ip k kp ↔ (x=2 ↔ xp=2) ∧
      i=colors x 0 ∧ ip=colors x 1 ∧ k=colors x 2 ∧ kp=colors x 3 := by
  have hc : ∀ x xp i ip k kp : Fin 3,
      Core x xp i ip k kp ↔ (x=2 ↔ xp=2) ∧
        i=colors x 0 ∧ ip=colors x 1 ∧ k=colors x 2 ∧ kp=colors x 3 := by unfold Core colors; decide
  exact hc x xp i ip k kp

def extension (x xp : Fin 3) : Fin 14 → Fin 3 :=
  ![x,xp,0,1,colors x 0,colors x 0,colors x 2,colors x 1,colors x 1,colors x 3,
    0,1,PlanarColoringExclusiveCrossing.third 0 (colors x 0),PlanarColoringExclusiveCrossing.third 1 (colors x 1)]

theorem proper_split (col : Fin 14 → Fin 3) : Proper col ↔
    PlanarColoringExclusiveCrossing.Proper (col ∘ topMap) ∧ PlanarColoringExclusiveCrossing.Proper (col ∘ bottomMap) ∧
      col 0≠col 4 ∧ col 0≠col 8 ∧ col 10≠col 6 ∧ col 6≠col 5 ∧ col 6≠col 8 ∧
      col 5≠col 9 ∧ col 8≠col 9 ∧ col 9≠col 11 ∧ col 7≠col 1 ∧ col 5≠col 1 := by
  simp only [Proper,graph,Sum.forall,Sum.elim_inl,Sum.elim_inr,Function.comp_apply]
  change (PlanarColoringExclusiveCrossing.Proper (col ∘ topMap) ∧ PlanarColoringExclusiveCrossing.Proper (col ∘ bottomMap) ∧ _) ↔ _
  simp [extraSrc,extraDst,Fin.forall_fin_succ,Matrix.cons_val_succ]

/-- All colorings with the stated reference palette have exactly the advertised
five port configurations, and each configuration has one full extension. -/
theorem proper_pinned_iff (col : Fin 14 → Fin 3) :
    Proper col ∧ col 2=0 ∧ col 3=1 ↔
      (col 0=2 ↔ col 1=2) ∧ col=extension (col 0) (col 1) := by
  constructor
  · rintro ⟨hp,hb,hg⟩
    obtain ⟨ht,hbot,hex⟩ := (proper_split col).mp hp
    obtain ⟨hneT,hT⟩ := (PlanarColoringExclusiveCrossing.proper_iff _).mp ht
    obtain ⟨hneB,hB⟩ := (PlanarColoringExclusiveCrossing.proper_iff _).mp hbot
    have h10 : col 10=0 := by
      have hh : col 2=col 10 := congrFun hT 2
      exact hh.symm.trans hb
    have h5 : col 5=col 4 := congrFun hT 3
    have h12 : col 12=PlanarColoringExclusiveCrossing.third 0 (col 4) := by
      have hh : col 12=PlanarColoringExclusiveCrossing.third (col 10) (col 4) := congrFun hT 4
      rwa [h10] at hh
    have h11 : col 11=1 := by
      have hh : col 11=col 3 := congrFun hB 2
      exact hh.trans hg
    have h7 : col 7=col 8 := congrFun hB 3
    have h13 : col 13=PlanarColoringExclusiveCrossing.third 1 (col 8) := by
      have hh : col 13=PlanarColoringExclusiveCrossing.third (col 3) (col 8) := congrFun hB 4
      rwa [hg] at hh
    have hcore : Core (col 0) (col 1) (col 4) (col 8) (col 6) (col 9) := by
      change col 10≠col 4 at hneT
      change col 3≠col 8 at hneB
      rw [h10] at hneT
      rw [hg] at hneB
      rcases hex with ⟨h0,h1,h2,h3,h4,h5',h6,h7',h8,h9⟩
      exact ⟨Ne.symm hneT,Ne.symm hneB,h0,h1,h10 ▸ h2,h5 ▸ h3,h4,h5 ▸ h5',h6,
        h11 ▸ h7',h7 ▸ h8,h5 ▸ h9⟩
    obtain ⟨hports,hi,hip,hk,hkp⟩ := (core_iff _ _ _ _ _ _).mp hcore
    refine ⟨hports,?_⟩
    funext v
    fin_cases v <;> dsimp [extension] <;> simp only [hb,hg,h10,h5,h12,h11,h7,h13,hi,hip,hk,hkp]
  · rintro ⟨hports,he⟩
    have hc := (core_iff (col 0) (col 1) (colors (col 0) 0) (colors (col 0) 1)
      (colors (col 0) 2) (colors (col 0) 3)).mpr ⟨hports,rfl,rfl,rfl,rfl⟩
    rw [he]
    refine ⟨(proper_split _).mpr ?_,rfl,rfl⟩
    rcases hc with ⟨hi,hip,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    refine ⟨?_,?_,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    · have h : extension (col 0) (col 1) ∘ topMap=PlanarColoringExclusiveCrossing.extension 0 (colors (col 0) 0) := by
        funext i
        fin_cases i <;> rfl
      rw [h]
      exact PlanarColoringExclusiveCrossing.extension_proper _ _ (Ne.symm hi)
    · have h : extension (col 0) (col 1) ∘ bottomMap=PlanarColoringExclusiveCrossing.extension 1 (colors (col 0) 1) := by
        funext i
        fin_cases i <;> rfl
      rw [h]
      exact PlanarColoringExclusiveCrossing.extension_proper _ _ (Ne.symm hip)

end PlanarHom.PlanarColoringTwoWayConverter
