import PlanarHom.MixedRelabelMachines
import PlanarHom.ListContextMachines
import PlanarHom.ListFlattenMachines

/-! Fixed finite label words compiled by genuine equality, context-map and
flatten machines. Empty words delete only their occurrence, never a vertex. -/
namespace PlanarHom.FiniteLabelWordLookupMachines
open Complexity

def lookup : List (ℕ × List ℕ) → ℕ → List ℕ
  | [], _ => []
  | (i,word)::table, n => if n=i then word else lookup table n

theorem fp_lookup (table : List (ℕ × List ℕ)) :
    FP BitEncoding.nat BitEncoding.nat.list (lookup table) := by
  induction table with
  | nil => exact fp_const _ _ []
  | cons entry table ih =>
    have hp := ((fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.nat entry.1)).comp
      PlanarHom.NatListSumMachines.fp_equal
    exact hp.ite (fp_const BitEncoding.nat BitEncoding.nat.list entry.2) ih

private theorem lookup_unique (table : List (ℕ × List ℕ)) (n : ℕ) (word : List ℕ)
    (hm : (n,word)∈table) (hu : ∀p∈table,p.1=n→p.2=word) : lookup table n=word := by
  induction table with
  | nil => simp at hm
  | cons p table ih =>
    by_cases hp : n=p.1
    · simpa [lookup,hp] using hu p (by simp) hp.symm
    · rw [lookup,if_neg hp]
      have ht : (n,word)∈table := by
        rcases List.mem_cons.mp hm with he | h
        · exact False.elim (hp (congrArg Prod.fst he))
        · exact h
      exact ih ht (fun q hq => hu q (List.mem_cons_of_mem _ hq))

def finTable {a b : ℕ} (ρ : Fin a→List (Fin b)) : List (ℕ × List ℕ) :=
  List.ofFn (fun i : Fin a => (i.val,(ρ i).map Fin.val))

theorem lookup_finTable {a b : ℕ} (ρ : Fin a→List (Fin b)) (i : Fin a) :
    lookup (finTable ρ) i.val=(ρ i).map Fin.val := by
  apply lookup_unique
  · exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · intro p hp he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
    have hij : j=i := Fin.ext he
    subst j
    rfl

theorem lookup_finTable_lt {a b : ℕ} (ρ : Fin a→List (Fin b)) (i : ℕ) (hi : i<a) :
    ∀j∈lookup (finTable ρ) i,j<b := by
  rw [lookup_finTable ρ ⟨i,hi⟩]
  intro j hj
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hj
  exact k.isLt

end PlanarHom.FiniteLabelWordLookupMachines

namespace PlanarHom.Complexity.MixedCode
open Turing
open PlanarHom.FiniteLabelWordLookupMachines
open PairProjectionMachines

def expandBinaryWords (table : List (ℕ × List ℕ)) (g : MixedCode) : MixedCode :=
  ⟨g.vertices,g.edges.flatMap (fun e =>
    (lookup table e.2.2).map (fun label => (e.1,e.2.1,label))),g.unaries⟩

theorem expandBinaryWords_valid (table : List (ℕ × List ℕ)) {g : MixedCode} {a b u : ℕ}
    (hg : g.Valid a u) (hlabels : ∀i,i<a→∀j∈lookup table i,j<b) :
    (g.expandBinaryWords table).Valid b u := by
  refine ⟨?_,hg.2⟩
  intro e he
  obtain ⟨old,hold,hword⟩ := List.mem_flatMap.mp he
  obtain ⟨label,hlabel,rfl⟩ := List.mem_map.mp hword
  have hv := hg.1 old hold
  exact ⟨hv.1,hv.2.1,hlabels _ hv.2.2 _ hlabel⟩

theorem fp_expandBinaryWords (table : List (ℕ × List ℕ)) :
    FP encoding encoding (expandBinaryWords table) := by
  let n := BitEncoding.nat
  let edge := n.prod (n.prod n)
  have hsrc := fp_fst n (n.prod n)
  have hdst := (fp_snd n (n.prod n)).comp (fp_fst n n)
  have hword := ((fp_snd n (n.prod n)).comp (fp_snd n n)).comp (fp_lookup table)
  have hcontext := hsrc.pair hdst
  have hiSrc := (fp_fst (n.prod n) n).comp (fp_fst n n)
  have hiDst := (fp_fst (n.prod n) n).comp (fp_snd n n)
  have hiLabel := fp_snd (n.prod n) n
  have hbody := hiSrc.pair (hiDst.pair hiLabel)
  have hitem := (hcontext.pair hword).comp
    (PlanarHom.ListContextMachines.fp_mapWithContext (n.prod n) n edge
      (fun p => (p.1.1,p.1.2,p.2)) hbody)
  have hlist := (fp_edges.comp (PlanarHom.ListMapMachines.fp_map edge edge.list
    (fun e => (lookup table e.2.2).map (fun label => (e.1,e.2.1,label))) hitem)).comp
      (PlanarHom.ListFlattenMachines.fp_flatten edge)
  have hout := fp_vertices.pair (hlist.pair fp_unaries)
  apply hout.transportOutput
  intro g
  rfl

noncomputable def expandBinaryWordsComputer (table : List (ℕ × List ℕ)) :
    TM2ComputableInPolyTime encoding.toFinEncoding encoding.toFinEncoding (expandBinaryWords table) :=
  Classical.choice (fp_expandBinaryWords table)

/-- Every successfully decoded raw word is normalized and transformed by an
actual ordinary machine, including noncanonical endpoint/label encodings. -/
noncomputable def expandBinaryWordsRawComputer (table : List (ℕ × List ℕ)) :
    TM2ComputableInPolyTime (BitEncoding.ValidWord.encoding encoding).toFinEncoding
      encoding.toFinEncoding (fun w => w.value.expandBinaryWords table) :=
  PlanarHom.MachineComposition.composeComputers normalizer (expandBinaryWordsComputer table)

noncomputable def expandBinaryWords_raw_outputs (table : List (ℕ × List ℕ)) (raw : Bits)
    (g : MixedCode) (hd : encoding.decode raw=some g) :
    TM2OutputsInTime (expandBinaryWordsRawComputer table).tm
      (raw.map (expandBinaryWordsRawComputer table).inputAlphabet.symm)
      (some ((encoding.encode (g.expandBinaryWords table)).map
        (expandBinaryWordsRawComputer table).outputAlphabet.symm))
      ((expandBinaryWordsRawComputer table).time.eval raw.length) := by
  let input : BitEncoding.ValidWord encoding := ⟨raw,⟨g,hd⟩⟩
  have hv : input.value=g := BitEncoding.ValidWord.value_eq hd
  have h := (expandBinaryWordsRawComputer table).outputsFun input
  simpa only [BitEncoding.toFinEncoding,BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw,hv,input] using h

end PlanarHom.Complexity.MixedCode
