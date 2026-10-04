import PlanarHom.Complexity

/-! Reuse an actual oracle reduction under proved promise/value transport,
without changing its program, time, or transcript. -/
namespace PlanarHom.Complexity

noncomputable def PromisePolyTimeTuringReduction.transport {T S : PromiseProblem}
    (r : PromisePolyTimeTuringReduction T S) (T' S' : PromiseProblem)
    (targetValid : ∀x,T'.valid x→T.valid x)
    (sourceValid : ∀x,S.valid x→S'.valid x)
    (targetValue : ∀x,T'.valid x→T'.value x=T.value x)
    (sourceValue : ∀x,S.valid x→S'.value x=S.value x) :
    PromisePolyTimeTuringReduction T' S' where
  machine:=r.machine
  time:=r.time
  computes oracle ho x hx:=by
    obtain ⟨steps,cost,qs,hr,hcost,hgood⟩:=r.computes oracle
      (fun q hq=>(ho q (sourceValid q hq)).trans (sourceValue q hq)) x (targetValid x hx)
    refine ⟨steps,cost,qs,?_,hcost,fun q a hqa=>sourceValid q (hgood q a hqa)⟩
    simpa only [targetValue x hx] using hr

end PlanarHom.Complexity
