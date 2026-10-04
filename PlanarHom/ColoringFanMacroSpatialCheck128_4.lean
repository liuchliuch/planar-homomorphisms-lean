import PlanarHom.ColoringFanMacroSpatialCheck128_3
noncomputable section
namespace PlanarHom.ColoringFanMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ee_400 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_894 edgeNode_975=true :=
  by decide +kernel

theorem self128_401 : edgeNode_976.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_395 self128_399 apart128_ee_400

theorem apart128_ee_402 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_731 edgeNode_976=true :=
  by decide +kernel

theorem apart128_ee_403 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_812 edgeNode_976=true :=
  by decide +kernel

theorem apart128_ee_404 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_813 edgeNode_976=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_402 apart128_ee_403

theorem self128_405 : edgeNode_977.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_391 self128_401 apart128_ee_404

theorem self128_406 : edgeNode_1016.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_407 : edgeNode_1057.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_408 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1016 edgeNode_1057=true :=
  by decide +kernel

theorem self128_409 : edgeNode_1058.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_406 self128_407 apart128_ee_408

theorem self128_410 : edgeNode_1097.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_411 : edgeNode_1138.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_412 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1097 edgeNode_1138=true :=
  by decide +kernel

theorem self128_413 : edgeNode_1139.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_410 self128_411 apart128_ee_412

theorem apart128_ee_414 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1058 edgeNode_1139=true :=
  by decide +kernel

theorem self128_415 : edgeNode_1140.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_409 self128_413 apart128_ee_414

theorem self128_416 : edgeNode_1179.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_417 : edgeNode_1220.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_418 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1179 edgeNode_1220=true :=
  by decide +kernel

theorem self128_419 : edgeNode_1221.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_416 self128_417 apart128_ee_418

theorem self128_420 : edgeNode_1260.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_421 : edgeNode_1301.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_422 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1260 edgeNode_1301=true :=
  by decide +kernel

theorem self128_423 : edgeNode_1302.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_420 self128_421 apart128_ee_422

theorem apart128_ee_424 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1221 edgeNode_1302=true :=
  by decide +kernel

theorem self128_425 : edgeNode_1303.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_419 self128_423 apart128_ee_424

theorem apart128_ee_426 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1058 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_427 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1139 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_428 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1140 edgeNode_1303=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_426 apart128_ee_427

theorem self128_429 : edgeNode_1304.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_415 self128_425 apart128_ee_428

theorem apart128_ee_430 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_653 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_431 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_653 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_432 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_653 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_430 apart128_ee_431

theorem apart128_ee_433 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_654 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_434 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_654 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_435 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_654 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_433 apart128_ee_434

theorem apart128_ee_436 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_655 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_432 apart128_ee_435

theorem apart128_ee_437 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_656 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_438 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_656 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_439 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_656 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_437 apart128_ee_438

theorem apart128_ee_440 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_657 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_441 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_657 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_442 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_657 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_440 apart128_ee_441

theorem apart128_ee_443 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_658 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_444 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_658 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_445 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_658 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_443 apart128_ee_444

theorem apart128_ee_446 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_659 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_442 apart128_ee_445

theorem apart128_ee_447 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_660 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_439 apart128_ee_446

theorem apart128_ee_448 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_661 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_436 apart128_ee_447

theorem apart128_ee_449 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_662 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_450 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_662 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_451 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_662 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_449 apart128_ee_450

theorem apart128_ee_452 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_663 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_453 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_663 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_454 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_663 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_452 apart128_ee_453

theorem apart128_ee_455 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_664 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_451 apart128_ee_454

theorem apart128_ee_456 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_665 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_457 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_665 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_458 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_665 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_456 apart128_ee_457

theorem apart128_ee_459 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_666 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_460 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_666 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_461 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_666 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_459 apart128_ee_460

theorem apart128_ee_462 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_667 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_463 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_667 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_464 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_667 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_462 apart128_ee_463

theorem apart128_ee_465 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_668 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_461 apart128_ee_464

theorem apart128_ee_466 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_669 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_458 apart128_ee_465

theorem apart128_ee_467 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_670 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_455 apart128_ee_466

theorem apart128_ee_468 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_671 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_448 apart128_ee_467

theorem apart128_ee_469 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_672 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_470 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_672 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_471 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_672 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_469 apart128_ee_470

theorem apart128_ee_472 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_673 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_473 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_673 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_474 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_673 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_472 apart128_ee_473

theorem apart128_ee_475 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_674 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_471 apart128_ee_474

theorem apart128_ee_476 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_675 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_477 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_675 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_478 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_675 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_476 apart128_ee_477

theorem apart128_ee_479 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_676 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_480 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_676 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_481 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_676 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_479 apart128_ee_480

theorem apart128_ee_482 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_677 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_483 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_677 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_484 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_677 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_482 apart128_ee_483

theorem apart128_ee_485 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_678 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_481 apart128_ee_484

theorem apart128_ee_486 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_679 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_478 apart128_ee_485

theorem apart128_ee_487 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_680 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_475 apart128_ee_486

theorem apart128_ee_488 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_681 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_489 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_681 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_490 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_681 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_488 apart128_ee_489

theorem apart128_ee_491 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_682 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_492 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_682 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_493 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_682 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_491 apart128_ee_492

theorem apart128_ee_494 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_683 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_490 apart128_ee_493

theorem apart128_ee_495 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_684 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_496 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_684 edgeNode_1303=true :=
  by decide +kernel

theorem apart128_ee_497 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_684 edgeNode_1304=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_495 apart128_ee_496

theorem apart128_ee_498 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_685 edgeNode_1140=true :=
  by decide +kernel

theorem apart128_ee_499 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_685 edgeNode_1303=true :=
  by decide +kernel

end PlanarHom.ColoringFanMacroCoordinates
