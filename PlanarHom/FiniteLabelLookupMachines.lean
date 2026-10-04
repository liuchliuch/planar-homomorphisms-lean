import PlanarHom.NatListSumMachines
import PlanarHom.ConditionalMachines

/-! Fixed finite label alias tables compiled from real binary equality tests
and finite-control selection, with a total zero default outside the table. -/
namespace PlanarHom.FiniteLabelLookupMachines
open PlanarHom.Complexity

def lookup : List (ℕ × ℕ)→ℕ→ℕ
  | [],_=>0
  | (i,j)::table,n=>if n=i then j else lookup table n

theorem fp_lookup (table : List (ℕ × ℕ)) : FP BitEncoding.nat BitEncoding.nat (lookup table):=by
  induction table with
  | nil=>exact fp_const _ _ 0
  | cons entry table ih=>
    have hp:=((fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.nat entry.1)).comp
      PlanarHom.NatListSumMachines.fp_equal
    exact hp.ite (fp_const BitEncoding.nat BitEncoding.nat entry.2) ih

theorem lookup_mem (table : List (ℕ × ℕ)) (n : ℕ) : lookup table n=0 ∨ (n,lookup table n)∈table:=by
  induction table with
  | nil=>exact Or.inl rfl
  | cons p table ih=>
    by_cases h:n=p.1
    · exact Or.inr (by simp [lookup,h])
    · simp only [lookup,if_neg h]
      rcases ih with hz | hm
      · exact Or.inl hz
      · exact Or.inr (List.mem_cons_of_mem _ hm)

end PlanarHom.FiniteLabelLookupMachines
