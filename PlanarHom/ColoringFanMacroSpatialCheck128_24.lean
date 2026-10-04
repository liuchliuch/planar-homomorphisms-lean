import PlanarHom.ColoringFanMacroSpatialCheck128_23
noncomputable section
namespace PlanarHom.ColoringFanMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ee_2400 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2161 edgeNode_2202=true :=
  by decide +kernel

theorem self128_2401 : edgeNode_2203.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2398 self128_2399 apart128_ee_2400

theorem self128_2402 : edgeNode_2242.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_2403 : edgeNode_2283.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_2404 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2242 edgeNode_2283=true :=
  by decide +kernel

theorem self128_2405 : edgeNode_2284.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2402 self128_2403 apart128_ee_2404

theorem apart128_ee_2406 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2203 edgeNode_2284=true :=
  by decide +kernel

theorem self128_2407 : edgeNode_2285.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2401 self128_2405 apart128_ee_2406

theorem apart128_ee_2408 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2040 edgeNode_2285=true :=
  by decide +kernel

theorem apart128_ee_2409 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2121 edgeNode_2285=true :=
  by decide +kernel

theorem apart128_ee_2410 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2122 edgeNode_2285=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2408 apart128_ee_2409

theorem self128_2411 : edgeNode_2286.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2397 self128_2407 apart128_ee_2410

theorem self128_2412 : edgeNode_2325.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_2413 : edgeNode_2366.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_2414 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2325 edgeNode_2366=true :=
  by decide +kernel

theorem self128_2415 : edgeNode_2367.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2412 self128_2413 apart128_ee_2414

theorem self128_2416 : edgeNode_2406.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_2417 : edgeNode_2447.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_2418 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2406 edgeNode_2447=true :=
  by decide +kernel

theorem self128_2419 : edgeNode_2448.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2416 self128_2417 apart128_ee_2418

theorem apart128_ee_2420 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2367 edgeNode_2448=true :=
  by decide +kernel

theorem self128_2421 : edgeNode_2449.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2415 self128_2419 apart128_ee_2420

theorem self128_2422 : edgeNode_2488.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_2423 : edgeNode_2529.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_2424 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2488 edgeNode_2529=true :=
  by decide +kernel

theorem self128_2425 : edgeNode_2530.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2422 self128_2423 apart128_ee_2424

theorem self128_2426 : edgeNode_2569.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_2427 : edgeNode_2610.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_2428 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2569 edgeNode_2610=true :=
  by decide +kernel

theorem self128_2429 : edgeNode_2611.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2426 self128_2427 apart128_ee_2428

theorem apart128_ee_2430 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2530 edgeNode_2611=true :=
  by decide +kernel

theorem self128_2431 : edgeNode_2612.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2425 self128_2429 apart128_ee_2430

theorem apart128_ee_2432 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2367 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2433 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2448 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2434 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2449 edgeNode_2612=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2432 apart128_ee_2433

theorem self128_2435 : edgeNode_2613.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_2421 self128_2431 apart128_ee_2434

theorem apart128_ee_2436 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1960 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2437 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1960 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2438 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1960 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2436 apart128_ee_2437

theorem apart128_ee_2439 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1961 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2440 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1961 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2441 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1961 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2439 apart128_ee_2440

theorem apart128_ee_2442 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1962 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2438 apart128_ee_2441

theorem apart128_ee_2443 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1963 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2444 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1963 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2445 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1963 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2443 apart128_ee_2444

theorem apart128_ee_2446 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1964 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2447 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1964 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2448 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1964 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2446 apart128_ee_2447

theorem apart128_ee_2449 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1965 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2450 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1965 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2451 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1965 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2449 apart128_ee_2450

theorem apart128_ee_2452 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1966 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2448 apart128_ee_2451

theorem apart128_ee_2453 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1967 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2445 apart128_ee_2452

theorem apart128_ee_2454 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1968 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2442 apart128_ee_2453

theorem apart128_ee_2455 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1969 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2456 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1969 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2457 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1969 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2455 apart128_ee_2456

theorem apart128_ee_2458 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1970 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2459 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1970 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2460 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1970 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2458 apart128_ee_2459

theorem apart128_ee_2461 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1971 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2457 apart128_ee_2460

theorem apart128_ee_2462 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1972 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2463 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1972 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2464 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1972 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2462 apart128_ee_2463

theorem apart128_ee_2465 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1973 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2466 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1973 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2467 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1973 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2465 apart128_ee_2466

theorem apart128_ee_2468 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1974 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2469 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1974 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2470 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1974 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2468 apart128_ee_2469

theorem apart128_ee_2471 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1975 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2467 apart128_ee_2470

theorem apart128_ee_2472 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1976 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2464 apart128_ee_2471

theorem apart128_ee_2473 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1977 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2461 apart128_ee_2472

theorem apart128_ee_2474 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1978 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2454 apart128_ee_2473

theorem apart128_ee_2475 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1979 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2476 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1979 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2477 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1979 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2475 apart128_ee_2476

theorem apart128_ee_2478 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1980 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2479 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1980 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2480 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1980 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2478 apart128_ee_2479

theorem apart128_ee_2481 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1981 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2477 apart128_ee_2480

theorem apart128_ee_2482 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1982 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2483 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1982 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2484 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1982 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2482 apart128_ee_2483

theorem apart128_ee_2485 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1983 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2486 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1983 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2487 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1983 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2485 apart128_ee_2486

theorem apart128_ee_2488 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1984 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2489 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1984 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2490 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1984 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2488 apart128_ee_2489

theorem apart128_ee_2491 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1985 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2487 apart128_ee_2490

theorem apart128_ee_2492 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1986 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2484 apart128_ee_2491

theorem apart128_ee_2493 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1987 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_2481 apart128_ee_2492

theorem apart128_ee_2494 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1988 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2495 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1988 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2496 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1988 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2494 apart128_ee_2495

theorem apart128_ee_2497 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1989 edgeNode_2449=true :=
  by decide +kernel

theorem apart128_ee_2498 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1989 edgeNode_2612=true :=
  by decide +kernel

theorem apart128_ee_2499 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1989 edgeNode_2613=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_2497 apart128_ee_2498

end PlanarHom.ColoringFanMacroCoordinates
