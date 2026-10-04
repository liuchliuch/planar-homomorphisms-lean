import PlanarHom.SurfaceBooleanFiniteRows

/-! NEW total encoded nullspace-extractor program, built from proved Gaussian
elimination and polynomial maps. Width is read from the materialized header. -/
namespace PlanarHom.SurfaceBooleanRows
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
abbrev indexCode := BitEncoding.bool.prod BitEncoding.nat
abbrev matrixCode := rowCode.prod rowCode.list

theorem fp_normalize : FP (rowCode.prod rowCode) rowCode (fun p => normalize p.1 p.2) := by
  have hr := fp_fst rowCode indexCode
  have hi := (fp_snd rowCode indexCode).comp (fp_snd BitEncoding.bool BitEncoding.nat)
  have hb := (hr.pair hi).comp fp_bitAt
  have hs := (fp_fst rowCode rowCode).comp (ListIndexMachines.fp_zipIdx BitEncoding.bool)
  have hx := fp_snd rowCode rowCode
  exact (hx.pair hs).comp (ListContextMachines.fp_mapWithContext rowCode indexCode BitEncoding.bool _ hb)

theorem fp_unit : FP (rowCode.prod BitEncoding.nat) rowCode (fun p => unit p.1 p.2) := by
  have hj := fp_fst BitEncoding.nat indexCode
  have hi := (fp_snd BitEncoding.nat indexCode).comp (fp_snd BitEncoding.bool BitEncoding.nat)
  have hb := (hi.pair hj).comp PfaffianList.fp_nat_eq
  have hs := (fp_fst rowCode BitEncoding.nat).comp (ListIndexMachines.fp_zipIdx BitEncoding.bool)
  have hx := fp_snd rowCode BitEncoding.nat
  exact (hx.pair hs).comp (ListContextMachines.fp_mapWithContext BitEncoding.nat indexCode BitEncoding.bool _ hb)

theorem fp_transpose : FP matrixCode rowCode.list (fun p => transpose p.1 p.2) := by
  have hi := fp_fst BitEncoding.nat rowCode
  have hr := fp_snd BitEncoding.nat rowCode
  have hb := (hr.pair hi).comp fp_bitAt
  have hm := ListContextMachines.fp_mapWithContext BitEncoding.nat rowCode BitEncoding.bool _ hb
  have hrows := fp_fst rowCode.list indexCode
  have hindex := (fp_snd rowCode.list indexCode).comp (fp_snd BitEncoding.bool BitEncoding.nat)
  have hcolumn := (hindex.pair hrows).comp hm
  have hshape := (fp_fst rowCode rowCode.list).comp (ListIndexMachines.fp_zipIdx BitEncoding.bool)
  have hinput := fp_snd rowCode rowCode.list
  exact (hinput.pair hshape).comp
    (ListContextMachines.fp_mapWithContext rowCode.list indexCode rowCode _ hcolumn)

theorem fp_normalizedRows : FP matrixCode rowCode.list (fun p => normalizedRows p.1 p.2) :=
  ListContextMachines.fp_mapWithContext rowCode rowCode rowCode _ fp_normalize

theorem fp_kernelRows : FP matrixCode rowCode.list (fun p => kernelRows p.1 p.2) := by
  let ec := rowCode.prod basisCode
  have hc := fp_fst ec indexCode
  have hshape := hc.comp (fp_fst rowCode basisCode)
  have hbs := hc.comp (fp_snd rowCode basisCode)
  have hi := (fp_snd ec indexCode).comp (fp_snd BitEncoding.bool BitEncoding.nat)
  have hunit := (hshape.pair hi).comp fp_unit
  have hbody := (hunit.pair hbs).comp fp_reduce
  have hs := fp_fst rowCode rowCode.list
  have hb := fp_normalizedRows.comp fp_basis
  have hindices := hs.comp (ListIndexMachines.fp_zipIdx BitEncoding.bool)
  have hcols := ((hs.pair hb).pair hindices).comp
    (ListContextMachines.fp_mapWithContext ec indexCode rowCode _ hbody)
  exact (hs.pair hcols).comp fp_transpose

end PlanarHom.SurfaceBooleanRows
