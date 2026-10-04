import PlanarHom.ColoringFanMacroSpatialCheck128_134
noncomputable section
namespace PlanarHom.ColoringFanMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ee_13500 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5025 edgeNode_5066=true :=
  by decide +kernel

theorem self128_13501 : edgeNode_5067.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13498 self128_13499 apart128_ee_13500

theorem apart128_ee_13502 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4986 edgeNode_5067=true :=
  by decide +kernel

theorem self128_13503 : edgeNode_5068.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13497 self128_13501 apart128_ee_13502

theorem self128_13504 : edgeNode_5107.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_13505 : edgeNode_5148.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_13506 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5107 edgeNode_5148=true :=
  by decide +kernel

theorem self128_13507 : edgeNode_5149.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13504 self128_13505 apart128_ee_13506

theorem self128_13508 : edgeNode_5188.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_13509 : edgeNode_5229.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_13510 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5188 edgeNode_5229=true :=
  by decide +kernel

theorem self128_13511 : edgeNode_5230.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13508 self128_13509 apart128_ee_13510

theorem apart128_ee_13512 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5149 edgeNode_5230=true :=
  by decide +kernel

theorem self128_13513 : edgeNode_5231.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13507 self128_13511 apart128_ee_13512

theorem apart128_ee_13514 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4986 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13515 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5067 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13516 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5068 edgeNode_5231=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13514 apart128_ee_13515

theorem self128_13517 : edgeNode_5232.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13503 self128_13513 apart128_ee_13516

theorem apart128_ee_13518 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4741 edgeNode_5232=true :=
  by decide +kernel

theorem apart128_ee_13519 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4822 edgeNode_5232=true :=
  by decide +kernel

theorem apart128_ee_13520 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4861 edgeNode_5232=true :=
  by decide +kernel

theorem apart128_ee_13521 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4864 edgeNode_5232=true :=
  by decide +kernel

theorem apart128_ee_13522 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4865 edgeNode_5232=true :=
  by decide +kernel

theorem apart128_ee_13523 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4866 edgeNode_5232=true :=
  by decide +kernel

theorem apart128_ee_13524 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4867 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13525 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4867 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13526 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4867 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13524 apart128_ee_13525

theorem apart128_ee_13527 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4868 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13523 apart128_ee_13526

theorem apart128_ee_13528 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4869 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13522 apart128_ee_13527

theorem apart128_ee_13529 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4870 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13521 apart128_ee_13528

theorem apart128_ee_13530 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4871 edgeNode_5232=true :=
  by decide +kernel

theorem apart128_ee_13531 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4872 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13532 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4872 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13533 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4872 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13531 apart128_ee_13532

theorem apart128_ee_13534 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4873 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13530 apart128_ee_13533

theorem apart128_ee_13535 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4874 edgeNode_5232=true :=
  by decide +kernel

theorem apart128_ee_13536 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4875 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13537 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4875 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13538 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4875 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13536 apart128_ee_13537

theorem apart128_ee_13539 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4876 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13540 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4876 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13541 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4876 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13539 apart128_ee_13540

theorem apart128_ee_13542 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4877 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13538 apart128_ee_13541

theorem apart128_ee_13543 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4878 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13535 apart128_ee_13542

theorem apart128_ee_13544 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4879 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13534 apart128_ee_13543

theorem apart128_ee_13545 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4880 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13529 apart128_ee_13544

theorem apart128_ee_13546 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4881 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13547 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4881 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13548 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4881 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13546 apart128_ee_13547

theorem apart128_ee_13549 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4882 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13550 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4882 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13551 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4882 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13549 apart128_ee_13550

theorem apart128_ee_13552 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4883 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13548 apart128_ee_13551

theorem apart128_ee_13553 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4884 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13554 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4884 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13555 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4884 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13553 apart128_ee_13554

theorem apart128_ee_13556 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4885 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13557 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4885 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13558 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4885 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13556 apart128_ee_13557

theorem apart128_ee_13559 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4886 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13560 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4886 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13561 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4886 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13559 apart128_ee_13560

theorem apart128_ee_13562 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4887 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13558 apart128_ee_13561

theorem apart128_ee_13563 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4888 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13555 apart128_ee_13562

theorem apart128_ee_13564 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4889 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13552 apart128_ee_13563

theorem apart128_ee_13565 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4890 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13566 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4890 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13567 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4890 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13565 apart128_ee_13566

theorem apart128_ee_13568 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4891 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13569 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4891 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13570 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4891 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13568 apart128_ee_13569

theorem apart128_ee_13571 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4892 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13572 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4892 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13573 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4892 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13571 apart128_ee_13572

theorem apart128_ee_13574 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4893 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13570 apart128_ee_13573

theorem apart128_ee_13575 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4894 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13567 apart128_ee_13574

theorem apart128_ee_13576 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4895 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13577 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4895 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13578 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4895 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13576 apart128_ee_13577

theorem apart128_ee_13579 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4896 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13580 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4896 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13581 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4896 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13579 apart128_ee_13580

theorem apart128_ee_13582 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4897 edgeNode_5068=true :=
  by decide +kernel

theorem apart128_ee_13583 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4897 edgeNode_5231=true :=
  by decide +kernel

theorem apart128_ee_13584 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4897 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13582 apart128_ee_13583

theorem apart128_ee_13585 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4898 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13581 apart128_ee_13584

theorem apart128_ee_13586 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4899 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13578 apart128_ee_13585

theorem apart128_ee_13587 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4900 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13575 apart128_ee_13586

theorem apart128_ee_13588 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4901 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13564 apart128_ee_13587

theorem apart128_ee_13589 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4902 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13545 apart128_ee_13588

theorem apart128_ee_13590 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4903 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13520 apart128_ee_13589

theorem apart128_ee_13591 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4904 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13519 apart128_ee_13590

theorem apart128_ee_13592 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4905 edgeNode_5232=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13518 apart128_ee_13591

theorem self128_13593 : edgeNode_5233.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13493 self128_13517 apart128_ee_13592

theorem apart128_ee_13594 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4004 edgeNode_5233=true :=
  by decide +kernel

theorem apart128_ee_13595 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4013 edgeNode_5233=true :=
  by decide +kernel

theorem apart128_ee_13596 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4016 edgeNode_5233=true :=
  by decide +kernel

theorem apart128_ee_13597 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4017 edgeNode_4741=true :=
  by decide +kernel

theorem apart128_ee_13598 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4017 edgeNode_4904=true :=
  by decide +kernel

theorem apart128_ee_13599 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4017 edgeNode_4905=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13597 apart128_ee_13598

end PlanarHom.ColoringFanMacroCoordinates
