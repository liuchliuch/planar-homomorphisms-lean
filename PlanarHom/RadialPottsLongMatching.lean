import PlanarHom.RadialPottsTile

/-! The exact endpoint equivalence proving that the constructed long edges
are a perfect matching, for every k, including k=0. -/
namespace PlanarHom.RadialPottsTile

def longEndpoint {k : ℕ} (p : Long k × Bool) : Vertex k :=
  if p.2 then longRight p.1 else .inl (longLeft p.1)

theorem longEndpoint_surjective (k : ℕ) : Function.Surjective (@longEndpoint k) := by
  intro v
  rcases v with ⟨r,i⟩ | ⟨s,a⟩
  · let side := i.val/(2*r.val+1)
    let pos := i.val%(2*r.val+1)
    have hs : side<4 := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
      have := i.isLt
      omega
    have hp : pos<2*r.val+1 := Nat.mod_lt _ (by omega)
    have hd : i.val=side*(2*r.val+1)+pos := by
      dsimp [side,pos]
      simpa only [Nat.mul_comm] using (Nat.div_add_mod i.val (2*r.val+1)).symm
    by_cases he : pos%2=0
    · let e : Long k := ⟨r,⟨⟨side,hs⟩,⟨pos/2,by omega⟩⟩⟩
      refine ⟨(e,false),?_⟩
      apply congrArg Sum.inl
      apply white_ext
      · rfl
      · change side*(2*r.val+1)+2*(pos/2)=i.val
        omega
    · have hr : 0<r.val := by omega
      let r' : Fin k := ⟨r.val-1,by have := r.isLt; omega⟩
      let e : Long k := ⟨r',⟨⟨side,hs⟩,⟨pos/2,by dsimp [r']; omega⟩⟩⟩
      have hr' : r'.val+1=r.val := by dsimp [r']; omega
      have hk : r'.val+1<k := hr' ▸ r.isLt
      refine ⟨(e,true),?_⟩
      change longRight e=Sum.inl ⟨r,i⟩
      rw [longRight,dif_pos hk]
      apply congrArg Sum.inl
      apply white_ext
      · exact hr'
      · change side*(2*(r'.val+1)+1)+2*(pos/2)+1=i.val
        rw [hr']
        omega
  · have hk : 0<k := by have := a.isLt; omega
    let r : Fin k := ⟨k-1,by omega⟩
    let e : Long k := ⟨r,⟨s,⟨a.val,by dsimp [r]; have := a.isLt; omega⟩⟩⟩
    have hn : ¬r.val+1<k := by dsimp [r]; omega
    refine ⟨(e,true),?_⟩
    change longRight e=Sum.inr ⟨s,a⟩
    rw [longRight,dif_neg hn]

theorem longEndpoint_bijective (k : ℕ) : Function.Bijective (@longEndpoint k) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨longEndpoint_surjective k,?_⟩
  rw [Fintype.card_prod,Fintype.card_bool,card_long,card_vertex]
  ring

noncomputable def longEndpointEquiv (k : ℕ) : (Long k × Bool) ≃ Vertex k :=
  Equiv.ofBijective _ (longEndpoint_bijective k)

end PlanarHom.RadialPottsTile
