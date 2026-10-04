import PlanarHom.PalettedColoringPatches

/-! NEW exact global palette decomposition for the literal shared-signal
port-patch coloring assembly. Each signal's triple is exposed by an actual
macro, and palettes are constant precisely along the generated signal relation. -/
noncomputable section
open Classical
namespace PlanarHom.PalettedColoringPatches
open MultiGraph ThreeColorPaletteCounting PlanarColoringClause
variable {C S : Type} {P W E : C→Type} [∀c,Nonempty (P c)]
variable (L : ∀c,Patch (P c) (W c) (E c)) (signal : ∀c,P c→S)

 def SharedMacro (s t : S) : Prop := ∃c,∃p q : P c,signal c p=s ∧ signal c q=t
 def signalSetoid : Setoid S := _root_.Relation.EqvGen.setoid (SharedMacro signal)
 abbrev SignalComponent := Quotient (signalSetoid signal)
 def signalComponent (s : S) : SignalComponent signal := Quotient.mk _ s
 abbrev GlobalBits := {b : S→Bool // ∀c,(L c).accepted (b ∘ signal c)}
 abbrev BoundaryAssignments := {b : S×Fin 3→Fin 3 // ∀c,Relation L signal c b}
 abbrev PaletteData := (SignalComponent signal→Palette) × GlobalBits L signal

 theorem component_ports (c : C) (p q : P c) : signalComponent signal (signal c p)=signalComponent signal (signal c q) :=
  Quotient.sound (_root_.Relation.EqvGen.rel _ _ ⟨c,p,q,rfl,rfl⟩)

 theorem triple_pair_injective : Function.Injective (fun t:Palette×Bool=>triple t.1 t.2) := by
  rintro ⟨p,b⟩ ⟨q,c⟩ he
  have hg:=congrFun he 1
  have hb:=congrFun he 2
  have hp:p=q:=Subtype.ext (Prod.ext hb hg)
  subst q
  have h:=congrFun he 0
  have hbc:b=c:=boolColor_injective ((palettePermutation p).injective h)
  subst c
  rfl

 def encodePaletteData (d : PaletteData L signal) : BoundaryAssignments L signal :=
  ⟨fun a=>triple (d.1 (signalComponent signal a.1)) (d.2.val a.1) a.2,by
    intro c
    let p₀:P c:=Classical.choice inferInstance
    refine ⟨⟨d.1 (signalComponent signal (signal c p₀)),⟨d.2.val ∘ signal c,d.2.property c⟩⟩,?_⟩
    funext a
    change triple (d.1 (signalComponent signal (signal c a.1))) (d.2.val (signal c a.1)) a.2=_
    rw [component_ports signal c a.1 p₀]
    rfl⟩

 theorem encodePaletteData_injective : Function.Injective (encodePaletteData L signal) := by
  intro d e h
  have hstate (s:S) : (d.1 (signalComponent signal s),d.2.val s)=(e.1 (signalComponent signal s),e.2.val s) := by
    apply triple_pair_injective
    funext k
    exact congrArg (fun b:BoundaryAssignments L signal=>b.val (s,k)) h
  apply Prod.ext
  · funext q
    induction q using Quotient.inductionOn with | _ s => exact congrArg Prod.fst (hstate s)
  · apply Subtype.ext
    funext s
    exact congrArg Prod.snd (hstate s)

 variable (cover : ∀s,∃c,∃p:P c,signal c p=s)

 def localState (b : BoundaryAssignments L signal) (c : C) : State (P c) (L c).accepted :=
  Classical.choose (b.property c)
 theorem localState_spec (b : BoundaryAssignments L signal) (c : C) :
    b.val ∘ placePort signal c=portColor (localState L signal b c) := Classical.choose_spec (b.property c)

 include cover in
 theorem signal_state_exists (b : BoundaryAssignments L signal) (s : S) :
    ∃t:Palette×Bool,∀k,triple t.1 t.2 k=b.val (s,k) := by
  obtain ⟨c,p,rfl⟩:=cover s
  refine ⟨((localState L signal b c).1,(localState L signal b c).2.val p),?_⟩
  intro k
  exact (congrFun (localState_spec L signal b c) (p,k)).symm

 def signalState (b : BoundaryAssignments L signal) (s : S) : Palette×Bool :=
  Classical.choose (signal_state_exists L signal cover b s)
 theorem signalState_spec (b : BoundaryAssignments L signal) (s : S) (k : Fin 3) :
    triple (signalState L signal cover b s).1 (signalState L signal cover b s).2 k=b.val (s,k) :=
  Classical.choose_spec (signal_state_exists L signal cover b s) k

 theorem signalState_port (b : BoundaryAssignments L signal) (c : C) (p : P c) :
    signalState L signal cover b (signal c p)=((localState L signal b c).1,(localState L signal b c).2.val p) := by
  apply triple_pair_injective
  funext k
  exact (signalState_spec L signal cover b (signal c p) k).trans
    (congrFun (localState_spec L signal b c) (p,k))

 theorem palette_respects (b : BoundaryAssignments L signal) {s t:S}
    (h : signalSetoid signal s t) :
    (signalState L signal cover b s).1=(signalState L signal cover b t).1 := by
  induction h with
  | rel s t h =>
      obtain ⟨c,p,q,rfl,rfl⟩:=h
      rw [signalState_port,signalState_port]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact ih.trans hj

 def decodedPalette (b : BoundaryAssignments L signal) : SignalComponent signal→Palette :=
  Quotient.lift (fun s=>(signalState L signal cover b s).1) (fun _ _ h=>palette_respects L signal cover b h)

 def decodedBits (b : BoundaryAssignments L signal) : GlobalBits L signal :=
  ⟨fun s=>(signalState L signal cover b s).2,by
    intro c
    have he:(fun p=>(signalState L signal cover b (signal c p)).2)=(localState L signal b c).2.val := by
      funext p
      exact congrArg Prod.snd (signalState_port L signal cover b c p)
    change (L c).accepted (fun p=>(signalState L signal cover b (signal c p)).2)
    rw [he]
    exact (localState L signal b c).2.property⟩

 def decodePaletteData (b : BoundaryAssignments L signal) : PaletteData L signal :=
  (decodedPalette L signal cover b,decodedBits L signal cover b)

 theorem encode_decode (b : BoundaryAssignments L signal) :
    encodePaletteData L signal (decodePaletteData L signal cover b)=b := by
  apply Subtype.ext
  funext a
  exact signalState_spec L signal cover b a.1 a.2

 def boundaryPaletteEquiv : BoundaryAssignments L signal ≃ PaletteData L signal where
  toFun:=decodePaletteData L signal cover
  invFun:=encodePaletteData L signal
  left_inv:=encode_decode L signal cover
  right_inv d:=encodePaletteData_injective L signal (encode_decode L signal cover (encodePaletteData L signal d))

 def coloringPaletteEquiv : Coloring (graph L signal) ≃ PaletteData L signal :=
  (coloringEquiv L signal).trans (boundaryPaletteEquiv L signal cover)

include cover in
 theorem coloring_palette_count [Finite S] :
    Nat.card (Coloring (graph L signal))=6^Nat.card (SignalComponent signal)*Nat.card (GlobalBits L signal) := by
  letI := Fintype.ofFinite S
  letI := Fintype.ofFinite (SignalComponent signal)
  rw [Nat.card_congr (coloringPaletteEquiv L signal cover)]
  simp only [PaletteData,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fun,palette_card]

end PlanarHom.PalettedColoringPatches
