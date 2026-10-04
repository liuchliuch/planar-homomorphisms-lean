import PlanarHom.ColoringCrossMacroSpatialCheck128_2
noncomputable section
namespace PlanarHom.ColoringCrossMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ee_300 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_380 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_301 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_380 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_302 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_380 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_300 apart128_ee_301

theorem apart128_ee_303 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_381 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_304 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_381 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_305 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_381 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_303 apart128_ee_304

theorem apart128_ee_306 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_382 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_302 apart128_ee_305

theorem apart128_ee_307 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_383 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_308 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_383 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_309 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_383 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_307 apart128_ee_308

theorem apart128_ee_310 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_384 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_311 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_384 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_312 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_384 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_310 apart128_ee_311

theorem apart128_ee_313 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_385 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_309 apart128_ee_312

theorem apart128_ee_314 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_386 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_306 apart128_ee_313

theorem apart128_ee_315 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_387 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_299 apart128_ee_314

theorem apart128_ee_316 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_388 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_292 apart128_ee_315

theorem apart128_ee_317 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_389 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_291 apart128_ee_316

theorem apart128_ee_318 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_390 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_290 apart128_ee_317

theorem apart128_ee_319 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_391 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_271 apart128_ee_318

theorem apart128_ee_320 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_392 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_192 apart128_ee_319

theorem self128_321 : edgeNode_786.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_27 self128_55 apart128_ee_320

theorem self128_322 : edgeNode_833.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_323 : edgeNode_882.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_324 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_833 edgeNode_882=true :=
  by decide +kernel

theorem self128_325 : edgeNode_883.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_322 self128_323 apart128_ee_324

theorem self128_326 : edgeNode_930.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_327 : edgeNode_979.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_328 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_930 edgeNode_979=true :=
  by decide +kernel

theorem self128_329 : edgeNode_980.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_326 self128_327 apart128_ee_328

theorem apart128_ee_330 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_883 edgeNode_980=true :=
  by decide +kernel

theorem self128_331 : edgeNode_981.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_325 self128_329 apart128_ee_330

theorem self128_332 : edgeNode_1028.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_333 : edgeNode_1077.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_334 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1028 edgeNode_1077=true :=
  by decide +kernel

theorem self128_335 : edgeNode_1078.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_332 self128_333 apart128_ee_334

theorem self128_336 : edgeNode_1127.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_337 : edgeNode_1176.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_338 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1127 edgeNode_1176=true :=
  by decide +kernel

theorem self128_339 : edgeNode_1177.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_336 self128_337 apart128_ee_338

theorem apart128_ee_340 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1078 edgeNode_1177=true :=
  by decide +kernel

theorem self128_341 : edgeNode_1178.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_335 self128_339 apart128_ee_340

theorem apart128_ee_342 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_833 edgeNode_1178=true :=
  by decide +kernel

theorem apart128_ee_343 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_882 edgeNode_1178=true :=
  by decide +kernel

theorem apart128_ee_344 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_883 edgeNode_1178=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_342 apart128_ee_343

theorem apart128_ee_345 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_930 edgeNode_1178=true :=
  by decide +kernel

theorem apart128_ee_346 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_979 edgeNode_1178=true :=
  by decide +kernel

theorem apart128_ee_347 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_980 edgeNode_1178=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_345 apart128_ee_346

theorem apart128_ee_348 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_981 edgeNode_1178=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_344 apart128_ee_347

theorem self128_349 : edgeNode_1179.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_331 self128_341 apart128_ee_348

theorem self128_350 : edgeNode_1226.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_351 : edgeNode_1275.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_352 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1226 edgeNode_1275=true :=
  by decide +kernel

theorem self128_353 : edgeNode_1276.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_350 self128_351 apart128_ee_352

theorem self128_354 : edgeNode_1323.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_355 : edgeNode_1372.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_356 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1323 edgeNode_1372=true :=
  by decide +kernel

theorem self128_357 : edgeNode_1373.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_354 self128_355 apart128_ee_356

theorem apart128_ee_358 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1276 edgeNode_1373=true :=
  by decide +kernel

theorem self128_359 : edgeNode_1374.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_353 self128_357 apart128_ee_358

theorem self128_360 : edgeNode_1421.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_361 : edgeNode_1470.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_362 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1421 edgeNode_1470=true :=
  by decide +kernel

theorem self128_363 : edgeNode_1471.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_360 self128_361 apart128_ee_362

theorem self128_364 : edgeNode_1520.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_365 : edgeNode_1569.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_366 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1520 edgeNode_1569=true :=
  by decide +kernel

theorem self128_367 : edgeNode_1570.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_364 self128_365 apart128_ee_366

theorem apart128_ee_368 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1471 edgeNode_1570=true :=
  by decide +kernel

theorem self128_369 : edgeNode_1571.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_363 self128_367 apart128_ee_368

theorem apart128_ee_370 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1276 edgeNode_1571=true :=
  by decide +kernel

theorem apart128_ee_371 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1323 edgeNode_1571=true :=
  by decide +kernel

theorem apart128_ee_372 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1372 edgeNode_1571=true :=
  by decide +kernel

theorem apart128_ee_373 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1373 edgeNode_1571=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_371 apart128_ee_372

theorem apart128_ee_374 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1374 edgeNode_1571=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_370 apart128_ee_373

theorem self128_375 : edgeNode_1572.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_359 self128_369 apart128_ee_374

theorem apart128_ee_376 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_833 edgeNode_1572=true :=
  by decide +kernel

theorem apart128_ee_377 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_856 edgeNode_1572=true :=
  by decide +kernel

theorem apart128_ee_378 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_867 edgeNode_1572=true :=
  by decide +kernel

theorem apart128_ee_379 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_872 edgeNode_1572=true :=
  by decide +kernel

theorem apart128_ee_380 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_873 edgeNode_1374=true :=
  by decide +kernel

theorem apart128_ee_381 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_873 edgeNode_1571=true :=
  by decide +kernel

theorem apart128_ee_382 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_873 edgeNode_1572=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_380 apart128_ee_381

theorem apart128_ee_383 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_874 edgeNode_1572=true :=
  by decide +kernel

theorem apart128_ee_384 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_875 edgeNode_1572=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_382 apart128_ee_383

theorem apart128_ee_385 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_878 edgeNode_1572=true :=
  by decide +kernel

theorem apart128_ee_386 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_879 edgeNode_1572=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_384 apart128_ee_385

theorem apart128_ee_387 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_880 edgeNode_1572=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_379 apart128_ee_386

theorem apart128_ee_388 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_881 edgeNode_1572=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_378 apart128_ee_387

theorem apart128_ee_389 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_882 edgeNode_1572=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_377 apart128_ee_388

theorem apart128_ee_390 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_883 edgeNode_1572=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_376 apart128_ee_389

theorem apart128_ee_391 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_906 edgeNode_1572=true :=
  by decide +kernel

theorem apart128_ee_392 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_917 edgeNode_1572=true :=
  by decide +kernel

theorem apart128_ee_393 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_922 edgeNode_1572=true :=
  by decide +kernel

theorem apart128_ee_394 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_923 edgeNode_1572=true :=
  by decide +kernel

theorem apart128_ee_395 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_924 edgeNode_1572=true :=
  by decide +kernel

theorem apart128_ee_396 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_925 edgeNode_1374=true :=
  by decide +kernel

theorem apart128_ee_397 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_925 edgeNode_1571=true :=
  by decide +kernel

theorem apart128_ee_398 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_925 edgeNode_1572=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_396 apart128_ee_397

theorem apart128_ee_399 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_926 edgeNode_1572=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_395 apart128_ee_398

end PlanarHom.ColoringCrossMacroCoordinates
