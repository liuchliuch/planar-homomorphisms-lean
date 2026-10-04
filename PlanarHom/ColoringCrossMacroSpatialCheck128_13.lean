import PlanarHom.ColoringCrossMacroSpatialCheck128_12
noncomputable section
namespace PlanarHom.ColoringCrossMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ee_1300 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2898 edgeNode_2947=true :=
  by decide +kernel

theorem self128_1301 : edgeNode_2948.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1298 self128_1299 apart128_ee_1300

theorem apart128_ee_1302 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2851 edgeNode_2948=true :=
  by decide +kernel

theorem self128_1303 : edgeNode_2949.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1297 self128_1301 apart128_ee_1302

theorem self128_1304 : edgeNode_2996.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1305 : edgeNode_3045.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1306 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2996 edgeNode_3045=true :=
  by decide +kernel

theorem self128_1307 : edgeNode_3046.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1304 self128_1305 apart128_ee_1306

theorem self128_1308 : edgeNode_3095.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1309 : edgeNode_3144.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1310 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_3095 edgeNode_3144=true :=
  by decide +kernel

theorem self128_1311 : edgeNode_3145.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1308 self128_1309 apart128_ee_1310

theorem apart128_ee_1312 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_3046 edgeNode_3145=true :=
  by decide +kernel

theorem self128_1313 : edgeNode_3146.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1307 self128_1311 apart128_ee_1312

theorem apart128_ee_1314 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2851 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1315 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2898 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1316 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2947 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1317 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2948 edgeNode_3146=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1315 apart128_ee_1316

theorem apart128_ee_1318 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2949 edgeNode_3146=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1314 apart128_ee_1317

theorem self128_1319 : edgeNode_3147.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1303 self128_1313 apart128_ee_1318

theorem apart128_ee_1320 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2458 edgeNode_3147=true :=
  by decide +kernel

theorem apart128_ee_1321 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2481 edgeNode_3147=true :=
  by decide +kernel

theorem apart128_ee_1322 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2482 edgeNode_3147=true :=
  by decide +kernel

theorem apart128_ee_1323 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2483 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1324 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2483 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1325 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2483 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1323 apart128_ee_1324

theorem apart128_ee_1326 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2484 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1327 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2484 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1328 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2484 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1326 apart128_ee_1327

theorem apart128_ee_1329 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2485 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1325 apart128_ee_1328

theorem apart128_ee_1330 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2486 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1322 apart128_ee_1329

theorem apart128_ee_1331 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2487 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1332 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2487 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1333 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2487 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1331 apart128_ee_1332

theorem apart128_ee_1334 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2488 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1335 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2488 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1336 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2488 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1334 apart128_ee_1335

theorem apart128_ee_1337 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2489 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1338 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2489 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1339 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2489 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1337 apart128_ee_1338

theorem apart128_ee_1340 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2490 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1336 apart128_ee_1339

theorem apart128_ee_1341 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2491 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1333 apart128_ee_1340

theorem apart128_ee_1342 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2492 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1330 apart128_ee_1341

theorem apart128_ee_1343 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2493 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1344 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2493 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1345 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2493 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1343 apart128_ee_1344

theorem apart128_ee_1346 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2494 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1347 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2494 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1348 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2494 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1346 apart128_ee_1347

theorem apart128_ee_1349 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2495 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1350 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2495 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1351 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2495 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1349 apart128_ee_1350

theorem apart128_ee_1352 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2496 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1348 apart128_ee_1351

theorem apart128_ee_1353 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2497 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1345 apart128_ee_1352

theorem apart128_ee_1354 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2498 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1355 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2498 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1356 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2498 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1354 apart128_ee_1355

theorem apart128_ee_1357 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2499 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1358 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2499 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1359 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2499 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1357 apart128_ee_1358

theorem apart128_ee_1360 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2500 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1361 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2500 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1362 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2500 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1360 apart128_ee_1361

theorem apart128_ee_1363 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2501 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1359 apart128_ee_1362

theorem apart128_ee_1364 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2502 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1356 apart128_ee_1363

theorem apart128_ee_1365 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2503 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1353 apart128_ee_1364

theorem apart128_ee_1366 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2504 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1342 apart128_ee_1365

theorem apart128_ee_1367 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2505 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1321 apart128_ee_1366

theorem apart128_ee_1368 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2506 edgeNode_3147=true :=
  by decide +kernel

theorem apart128_ee_1369 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2507 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1370 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2507 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1371 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2507 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1369 apart128_ee_1370

theorem apart128_ee_1372 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2508 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1373 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2508 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1374 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2508 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1372 apart128_ee_1373

theorem apart128_ee_1375 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2509 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1371 apart128_ee_1374

theorem apart128_ee_1376 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2510 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1368 apart128_ee_1375

theorem apart128_ee_1377 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2511 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1378 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2511 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1379 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2511 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1377 apart128_ee_1378

theorem apart128_ee_1380 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2512 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1381 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2512 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1382 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2512 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1380 apart128_ee_1381

theorem apart128_ee_1383 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2513 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1384 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2513 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1385 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2513 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1383 apart128_ee_1384

theorem apart128_ee_1386 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2514 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1382 apart128_ee_1385

theorem apart128_ee_1387 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2515 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1379 apart128_ee_1386

theorem apart128_ee_1388 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2516 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1376 apart128_ee_1387

theorem apart128_ee_1389 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2517 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1390 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2517 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1391 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2517 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1389 apart128_ee_1390

theorem apart128_ee_1392 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2518 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1393 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2518 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1394 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2518 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1392 apart128_ee_1393

theorem apart128_ee_1395 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2519 edgeNode_2949=true :=
  by decide +kernel

theorem apart128_ee_1396 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2519 edgeNode_3146=true :=
  by decide +kernel

theorem apart128_ee_1397 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2519 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1395 apart128_ee_1396

theorem apart128_ee_1398 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2520 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1394 apart128_ee_1397

theorem apart128_ee_1399 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2521 edgeNode_3147=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1391 apart128_ee_1398

end PlanarHom.ColoringCrossMacroCoordinates
