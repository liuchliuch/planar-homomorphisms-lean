import PlanarHom.ColoringWireMacroSpatialCheck128_2
noncomputable section
namespace PlanarHom.ColoringWireMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ee_300 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_322 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_276 apart128_ee_299

theorem apart128_ee_301 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_323 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_257 apart128_ee_300

theorem apart128_ee_302 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_324 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_218 apart128_ee_301

theorem apart128_ee_303 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_325 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_139 apart128_ee_302

theorem apart128_ee_304 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_326 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_64 apart128_ee_303

theorem self128_305 : edgeNode_654.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_23 self128_47 apart128_ee_304

theorem self128_306 : edgeNode_693.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_307 : edgeNode_734.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_308 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_693 edgeNode_734=true :=
  by decide +kernel

theorem self128_309 : edgeNode_735.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_306 self128_307 apart128_ee_308

theorem self128_310 : edgeNode_774.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_311 : edgeNode_815.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_312 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_774 edgeNode_815=true :=
  by decide +kernel

theorem self128_313 : edgeNode_816.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_310 self128_311 apart128_ee_312

theorem apart128_ee_314 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_735 edgeNode_816=true :=
  by decide +kernel

theorem self128_315 : edgeNode_817.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_309 self128_313 apart128_ee_314

theorem self128_316 : edgeNode_856.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_317 : edgeNode_897.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_318 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_856 edgeNode_897=true :=
  by decide +kernel

theorem self128_319 : edgeNode_898.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_316 self128_317 apart128_ee_318

theorem self128_320 : edgeNode_937.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_321 : edgeNode_978.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_322 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_937 edgeNode_978=true :=
  by decide +kernel

theorem self128_323 : edgeNode_979.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_320 self128_321 apart128_ee_322

theorem apart128_ee_324 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_898 edgeNode_979=true :=
  by decide +kernel

theorem self128_325 : edgeNode_980.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_319 self128_323 apart128_ee_324

theorem apart128_ee_326 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_735 edgeNode_980=true :=
  by decide +kernel

theorem apart128_ee_327 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_816 edgeNode_980=true :=
  by decide +kernel

theorem apart128_ee_328 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_817 edgeNode_980=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_326 apart128_ee_327

theorem self128_329 : edgeNode_981.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_315 self128_325 apart128_ee_328

theorem self128_330 : edgeNode_1020.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_331 : edgeNode_1061.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_332 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1020 edgeNode_1061=true :=
  by decide +kernel

theorem self128_333 : edgeNode_1062.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_330 self128_331 apart128_ee_332

theorem self128_334 : edgeNode_1101.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_335 : edgeNode_1142.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_336 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1101 edgeNode_1142=true :=
  by decide +kernel

theorem self128_337 : edgeNode_1143.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_334 self128_335 apart128_ee_336

theorem apart128_ee_338 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1062 edgeNode_1143=true :=
  by decide +kernel

theorem self128_339 : edgeNode_1144.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_333 self128_337 apart128_ee_338

theorem self128_340 : edgeNode_1183.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_341 : edgeNode_1224.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_342 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1183 edgeNode_1224=true :=
  by decide +kernel

theorem self128_343 : edgeNode_1225.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_340 self128_341 apart128_ee_342

theorem self128_344 : edgeNode_1264.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_345 : edgeNode_1305.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_346 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1264 edgeNode_1305=true :=
  by decide +kernel

theorem self128_347 : edgeNode_1306.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_344 self128_345 apart128_ee_346

theorem apart128_ee_348 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1225 edgeNode_1306=true :=
  by decide +kernel

theorem self128_349 : edgeNode_1307.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_343 self128_347 apart128_ee_348

theorem apart128_ee_350 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1062 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_351 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1143 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_352 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1144 edgeNode_1307=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_350 apart128_ee_351

theorem self128_353 : edgeNode_1308.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_339 self128_349 apart128_ee_352

theorem apart128_ee_354 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_655 edgeNode_1144=true :=
  by decide +kernel

theorem apart128_ee_355 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_655 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_356 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_655 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_354 apart128_ee_355

theorem apart128_ee_357 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_656 edgeNode_1144=true :=
  by decide +kernel

theorem apart128_ee_358 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_656 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_359 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_656 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_357 apart128_ee_358

theorem apart128_ee_360 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_657 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_356 apart128_ee_359

theorem apart128_ee_361 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_658 edgeNode_1144=true :=
  by decide +kernel

theorem apart128_ee_362 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_658 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_363 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_658 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_361 apart128_ee_362

theorem apart128_ee_364 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_659 edgeNode_1144=true :=
  by decide +kernel

theorem apart128_ee_365 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_659 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_366 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_659 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_364 apart128_ee_365

theorem apart128_ee_367 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_660 edgeNode_1144=true :=
  by decide +kernel

theorem apart128_ee_368 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_660 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_369 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_660 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_367 apart128_ee_368

theorem apart128_ee_370 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_661 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_366 apart128_ee_369

theorem apart128_ee_371 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_662 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_363 apart128_ee_370

theorem apart128_ee_372 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_663 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_360 apart128_ee_371

theorem apart128_ee_373 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_664 edgeNode_1144=true :=
  by decide +kernel

theorem apart128_ee_374 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_664 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_375 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_664 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_373 apart128_ee_374

theorem apart128_ee_376 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_665 edgeNode_1144=true :=
  by decide +kernel

theorem apart128_ee_377 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_665 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_378 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_665 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_376 apart128_ee_377

theorem apart128_ee_379 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_666 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_375 apart128_ee_378

theorem apart128_ee_380 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_667 edgeNode_1144=true :=
  by decide +kernel

theorem apart128_ee_381 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_667 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_382 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_667 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_380 apart128_ee_381

theorem apart128_ee_383 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_668 edgeNode_1144=true :=
  by decide +kernel

theorem apart128_ee_384 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_668 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_385 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_668 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_383 apart128_ee_384

theorem apart128_ee_386 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_669 edgeNode_1144=true :=
  by decide +kernel

theorem apart128_ee_387 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_669 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_388 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_669 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_386 apart128_ee_387

theorem apart128_ee_389 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_670 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_385 apart128_ee_388

theorem apart128_ee_390 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_671 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_382 apart128_ee_389

theorem apart128_ee_391 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_672 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_379 apart128_ee_390

theorem apart128_ee_392 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_673 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_372 apart128_ee_391

theorem apart128_ee_393 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_674 edgeNode_1144=true :=
  by decide +kernel

theorem apart128_ee_394 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_674 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_395 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_674 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_393 apart128_ee_394

theorem apart128_ee_396 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_675 edgeNode_1144=true :=
  by decide +kernel

theorem apart128_ee_397 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_675 edgeNode_1307=true :=
  by decide +kernel

theorem apart128_ee_398 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_675 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_396 apart128_ee_397

theorem apart128_ee_399 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_676 edgeNode_1308=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_395 apart128_ee_398

end PlanarHom.ColoringWireMacroCoordinates
