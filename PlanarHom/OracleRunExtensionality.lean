import PlanarHom.Complexity

/-! A finite oracle execution depends only on its recorded answers, enabling
full all-valid-extension promise semantics without assuming values elsewhere. -/
namespace PlanarHom.Complexity.OracleTM2.Run

/-- Replace the oracle by any function agreeing on the actual transcript. -/
theorem changeOracle {m : OracleTM2} {oracle replacement : Bits→Bits}
    {c d : m.Cfg} {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (h : m.Run oracle c d steps cost qs)
    (answers : ∀q a,(q,a)∈qs→ replacement q=a) :
    m.Run replacement c d steps cost qs:=by
  induction h with
  | refl c=>exact .refl c
  | ordinary hn ht hr ih=>exact .ordinary hn ht (ih answers)
  | @query c z steps cost qs next hq hr ih=>
    have hanswer : replacement (m.queryWord c)=oracle (m.queryWord c):=
      answers _ _ (by simp)
    have he : m.answerCfg replacement c next=m.answerCfg oracle c next:=by
      simp only [OracleTM2.answerCfg,hanswer]
    have hrest:=ih (fun q a ha=>answers q a (List.mem_cons_of_mem _ ha))
    rw [←he] at hrest
    have hh:=OracleTM2.Run.query next hq hrest
    simpa only [hanswer] using hh

end PlanarHom.Complexity.OracleTM2.Run
