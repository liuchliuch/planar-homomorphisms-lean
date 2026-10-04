import PlanarHom.ColoringWireMacroSpatialCheck128_24
noncomputable section
namespace PlanarHom.ColoringWireMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ee_2500 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2258 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2501 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2258 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2502 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2258 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2500 apart128_ee_2501

theorem apart128_ee_2503 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2259 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2504 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2259 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2505 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2259 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2503 apart128_ee_2504

theorem apart128_ee_2506 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2260 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2502 apart128_ee_2505

theorem apart128_ee_2507 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2261 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2508 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2261 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2509 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2261 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2507 apart128_ee_2508

theorem apart128_ee_2510 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2262 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2511 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2262 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2512 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2262 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2510 apart128_ee_2511

theorem apart128_ee_2513 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2263 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2514 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2263 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2515 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2263 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2513 apart128_ee_2514

theorem apart128_ee_2516 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2264 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2512 apart128_ee_2515

theorem apart128_ee_2517 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2265 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2509 apart128_ee_2516

theorem apart128_ee_2518 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2266 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2506 apart128_ee_2517

theorem apart128_ee_2519 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2267 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2499 apart128_ee_2518

theorem apart128_ee_2520 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2268 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2521 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2268 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2522 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2268 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2520 apart128_ee_2521

theorem apart128_ee_2523 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2269 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2524 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2269 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2525 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2269 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2523 apart128_ee_2524

theorem apart128_ee_2526 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2270 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2522 apart128_ee_2525

theorem apart128_ee_2527 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2271 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2528 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2271 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2529 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2271 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2527 apart128_ee_2528

theorem apart128_ee_2530 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2272 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2531 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2272 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2532 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2272 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2530 apart128_ee_2531

theorem apart128_ee_2533 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2273 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2534 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2273 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2535 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2273 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2533 apart128_ee_2534

theorem apart128_ee_2536 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2274 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2532 apart128_ee_2535

theorem apart128_ee_2537 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2275 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2529 apart128_ee_2536

theorem apart128_ee_2538 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2276 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2526 apart128_ee_2537

theorem apart128_ee_2539 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2277 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2540 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2277 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2541 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2277 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2539 apart128_ee_2540

theorem apart128_ee_2542 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2278 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2543 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2278 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2544 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2278 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2542 apart128_ee_2543

theorem apart128_ee_2545 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2279 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2546 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2279 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2547 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2279 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2545 apart128_ee_2546

theorem apart128_ee_2548 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2280 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2544 apart128_ee_2547

theorem apart128_ee_2549 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2281 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2541 apart128_ee_2548

theorem apart128_ee_2550 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2282 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2551 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2282 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2552 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2282 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2550 apart128_ee_2551

theorem apart128_ee_2553 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2283 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2554 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2283 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2555 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2283 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2553 apart128_ee_2554

theorem apart128_ee_2556 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2284 edgeNode_2455=true :=
  by decide +kernel

theorem apart128_ee_2557 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2284 edgeNode_2620=true :=
  by decide +kernel

theorem apart128_ee_2558 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2284 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2556 apart128_ee_2557

theorem apart128_ee_2559 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2285 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2555 apart128_ee_2558

theorem apart128_ee_2560 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2286 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2552 apart128_ee_2559

theorem apart128_ee_2561 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2287 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2549 apart128_ee_2560

theorem apart128_ee_2562 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2288 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2538 apart128_ee_2561

theorem apart128_ee_2563 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2289 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2519 apart128_ee_2562

theorem apart128_ee_2564 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2290 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2480 apart128_ee_2563

theorem apart128_ee_2565 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2291 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2401 apart128_ee_2564

theorem apart128_ee_2566 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2292 edgeNode_2621=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2330 apart128_ee_2565

theorem self128_2567 : edgeNode_2622.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2289 self128_2313 apart128_ee_2566

theorem apart128_ee_2568 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1311 edgeNode_2128=true :=
  by decide +kernel

theorem apart128_ee_2569 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1311 edgeNode_2291=true :=
  by decide +kernel

theorem apart128_ee_2570 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1311 edgeNode_2292=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2568 apart128_ee_2569

theorem apart128_ee_2571 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1311 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2572 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1311 edgeNode_2622=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2570 apart128_ee_2571

theorem apart128_ee_2573 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1312 edgeNode_2128=true :=
  by decide +kernel

theorem apart128_ee_2574 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1312 edgeNode_2291=true :=
  by decide +kernel

theorem apart128_ee_2575 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1312 edgeNode_2292=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2573 apart128_ee_2574

theorem apart128_ee_2576 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1312 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2577 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1312 edgeNode_2622=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2575 apart128_ee_2576

theorem apart128_ee_2578 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1313 edgeNode_2622=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2572 apart128_ee_2577

theorem apart128_ee_2579 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1314 edgeNode_2128=true :=
  by decide +kernel

theorem apart128_ee_2580 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1314 edgeNode_2291=true :=
  by decide +kernel

theorem apart128_ee_2581 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1314 edgeNode_2292=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2579 apart128_ee_2580

theorem apart128_ee_2582 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1314 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2583 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1314 edgeNode_2622=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2581 apart128_ee_2582

theorem apart128_ee_2584 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1315 edgeNode_2128=true :=
  by decide +kernel

theorem apart128_ee_2585 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1315 edgeNode_2291=true :=
  by decide +kernel

theorem apart128_ee_2586 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1315 edgeNode_2292=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2584 apart128_ee_2585

theorem apart128_ee_2587 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1315 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2588 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1315 edgeNode_2622=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2586 apart128_ee_2587

theorem apart128_ee_2589 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1316 edgeNode_2128=true :=
  by decide +kernel

theorem apart128_ee_2590 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1316 edgeNode_2291=true :=
  by decide +kernel

theorem apart128_ee_2591 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1316 edgeNode_2292=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2589 apart128_ee_2590

theorem apart128_ee_2592 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1316 edgeNode_2621=true :=
  by decide +kernel

theorem apart128_ee_2593 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1316 edgeNode_2622=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2591 apart128_ee_2592

theorem apart128_ee_2594 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1317 edgeNode_2622=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2588 apart128_ee_2593

theorem apart128_ee_2595 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1318 edgeNode_2622=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2583 apart128_ee_2594

theorem apart128_ee_2596 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1319 edgeNode_2622=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2578 apart128_ee_2595

theorem apart128_ee_2597 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1320 edgeNode_2128=true :=
  by decide +kernel

theorem apart128_ee_2598 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1320 edgeNode_2291=true :=
  by decide +kernel

theorem apart128_ee_2599 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1320 edgeNode_2292=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2597 apart128_ee_2598

end PlanarHom.ColoringWireMacroCoordinates
