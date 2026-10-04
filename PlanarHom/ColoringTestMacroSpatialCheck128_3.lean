import PlanarHom.ColoringTestMacroSpatialCheck128_2
noncomputable section
namespace PlanarHom.ColoringTestMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ee_300 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_250 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_301 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_250 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_302 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_250 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_300 apart128_ee_301

theorem apart128_ee_303 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_251 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_304 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_251 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_305 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_251 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_303 apart128_ee_304

theorem apart128_ee_306 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_252 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_302 apart128_ee_305

theorem apart128_ee_307 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_253 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_308 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_253 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_309 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_253 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_307 apart128_ee_308

theorem apart128_ee_310 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_254 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_311 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_254 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_312 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_254 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_310 apart128_ee_311

theorem apart128_ee_313 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_255 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_309 apart128_ee_312

theorem apart128_ee_314 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_256 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_306 apart128_ee_313

theorem apart128_ee_315 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_257 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_316 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_257 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_317 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_257 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_315 apart128_ee_316

theorem apart128_ee_318 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_258 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_319 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_258 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_320 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_258 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_318 apart128_ee_319

theorem apart128_ee_321 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_259 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_317 apart128_ee_320

theorem apart128_ee_322 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_260 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_323 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_260 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_324 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_260 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_322 apart128_ee_323

theorem apart128_ee_325 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_261 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_326 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_261 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_327 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_261 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_325 apart128_ee_326

theorem apart128_ee_328 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_262 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_329 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_262 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_330 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_262 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_328 apart128_ee_329

theorem apart128_ee_331 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_263 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_327 apart128_ee_330

theorem apart128_ee_332 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_264 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_324 apart128_ee_331

theorem apart128_ee_333 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_265 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_321 apart128_ee_332

theorem apart128_ee_334 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_266 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_314 apart128_ee_333

theorem apart128_ee_335 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_267 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_299 apart128_ee_334

theorem apart128_ee_336 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_268 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_268 apart128_ee_335

theorem apart128_ee_337 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_269 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_201 apart128_ee_336

theorem apart128_ee_338 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_270 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_98 apart128_ee_337

theorem self128_339 : edgeNode_542.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_23 self128_47 apart128_ee_338

theorem apart128_ev_340 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_14 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_341 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_31 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_342 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_32 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_340 apart128_ev_341

theorem apart128_ev_343 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_47 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_344 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_64 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_345 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_65 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_343 apart128_ev_344

theorem apart128_ev_346 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_66 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_342 apart128_ev_345

theorem apart128_ev_347 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_81 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_348 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_98 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_349 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_99 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_347 apart128_ev_348

theorem apart128_ev_350 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_114 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_351 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_131 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_352 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_132 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_350 apart128_ev_351

theorem apart128_ev_353 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_133 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_349 apart128_ev_352

theorem apart128_ev_354 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_134 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_346 apart128_ev_353

theorem apart128_ev_355 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_149 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_356 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_166 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_357 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_167 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_355 apart128_ev_356

theorem apart128_ev_358 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_182 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_359 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_199 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_360 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_200 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_358 apart128_ev_359

theorem apart128_ev_361 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_201 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_357 apart128_ev_360

theorem apart128_ev_362 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_216 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_363 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_233 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_364 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_234 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_362 apart128_ev_363

theorem apart128_ev_365 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_249 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_366 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_266 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_367 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_267 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_365 apart128_ev_366

theorem apart128_ev_368 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_268 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_364 apart128_ev_367

theorem apart128_ev_369 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_269 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_361 apart128_ev_368

theorem apart128_ev_370 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_270 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_354 apart128_ev_369

theorem apart128_ev_371 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_285 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_372 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_302 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_373 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_303 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_371 apart128_ev_372

theorem apart128_ev_374 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_318 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_375 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_335 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_376 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_336 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_374 apart128_ev_375

theorem apart128_ev_377 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_337 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_373 apart128_ev_376

theorem apart128_ev_378 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_352 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_379 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_369 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_380 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_370 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_378 apart128_ev_379

theorem apart128_ev_381 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_385 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_382 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_402 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_383 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_403 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_381 apart128_ev_382

theorem apart128_ev_384 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_404 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_380 apart128_ev_383

theorem apart128_ev_385 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_405 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_377 apart128_ev_384

theorem apart128_ev_386 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_420 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_387 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_437 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_388 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_438 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_386 apart128_ev_387

theorem apart128_ev_389 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_453 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_390 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_470 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_391 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_471 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_389 apart128_ev_390

theorem apart128_ev_392 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_472 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_388 apart128_ev_391

theorem apart128_ev_393 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_487 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_394 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_504 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_395 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_505 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_393 apart128_ev_394

theorem apart128_ev_396 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_520 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_397 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_537 vertexNode_226=true :=
  by decide +kernel

theorem apart128_ev_398 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_538 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_396 apart128_ev_397

theorem apart128_ev_399 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_539 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_395 apart128_ev_398

end PlanarHom.ColoringTestMacroCoordinates
