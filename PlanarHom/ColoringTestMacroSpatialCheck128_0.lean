import PlanarHom.ColoringTestMacroSpatialData
noncomputable section
namespace PlanarHom.ColoringTestMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem self128_0 : edgeNode_32.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1 : edgeNode_65.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_2 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_32 edgeNode_65=true :=
  by decide +kernel

theorem self128_3 : edgeNode_66.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_0 self128_1 apart128_ee_2

theorem self128_4 : edgeNode_99.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_5 : edgeNode_132.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_6 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_99 edgeNode_132=true :=
  by decide +kernel

theorem self128_7 : edgeNode_133.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_4 self128_5 apart128_ee_6

theorem apart128_ee_8 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_66 edgeNode_133=true :=
  by decide +kernel

theorem self128_9 : edgeNode_134.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_3 self128_7 apart128_ee_8

theorem self128_10 : edgeNode_167.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_11 : edgeNode_200.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_12 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_167 edgeNode_200=true :=
  by decide +kernel

theorem self128_13 : edgeNode_201.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_10 self128_11 apart128_ee_12

theorem self128_14 : edgeNode_234.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_15 : edgeNode_267.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_16 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_234 edgeNode_267=true :=
  by decide +kernel

theorem self128_17 : edgeNode_268.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_14 self128_15 apart128_ee_16

theorem apart128_ee_18 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_201 edgeNode_268=true :=
  by decide +kernel

theorem self128_19 : edgeNode_269.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13 self128_17 apart128_ee_18

theorem apart128_ee_20 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_66 edgeNode_269=true :=
  by decide +kernel

theorem apart128_ee_21 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_133 edgeNode_269=true :=
  by decide +kernel

theorem apart128_ee_22 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_134 edgeNode_269=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_20 apart128_ee_21

theorem self128_23 : edgeNode_270.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_9 self128_19 apart128_ee_22

theorem self128_24 : edgeNode_303.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_25 : edgeNode_336.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_26 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_303 edgeNode_336=true :=
  by decide +kernel

theorem self128_27 : edgeNode_337.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_24 self128_25 apart128_ee_26

theorem self128_28 : edgeNode_370.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_29 : edgeNode_403.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_30 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_370 edgeNode_403=true :=
  by decide +kernel

theorem self128_31 : edgeNode_404.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_28 self128_29 apart128_ee_30

theorem apart128_ee_32 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_337 edgeNode_404=true :=
  by decide +kernel

theorem self128_33 : edgeNode_405.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_27 self128_31 apart128_ee_32

theorem self128_34 : edgeNode_438.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_35 : edgeNode_471.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_36 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_438 edgeNode_471=true :=
  by decide +kernel

theorem self128_37 : edgeNode_472.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_34 self128_35 apart128_ee_36

theorem self128_38 : edgeNode_505.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_39 : edgeNode_538.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_40 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_505 edgeNode_538=true :=
  by decide +kernel

theorem self128_41 : edgeNode_539.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_38 self128_39 apart128_ee_40

theorem apart128_ee_42 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_472 edgeNode_539=true :=
  by decide +kernel

theorem self128_43 : edgeNode_540.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_37 self128_41 apart128_ee_42

theorem apart128_ee_44 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_337 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_45 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_404 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_46 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_405 edgeNode_540=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_44 apart128_ee_45

theorem self128_47 : edgeNode_541.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_33 self128_43 apart128_ee_46

theorem apart128_ee_48 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_6 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_49 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_9 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_50 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_10 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_51 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_11 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_52 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_11 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_53 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_11 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_51 apart128_ee_52

theorem apart128_ee_54 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_12 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_50 apart128_ee_53

theorem apart128_ee_55 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_13 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_49 apart128_ee_54

theorem apart128_ee_56 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_14 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_48 apart128_ee_55

theorem apart128_ee_57 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_31 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_58 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_32 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_56 apart128_ee_57

theorem apart128_ee_59 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_65 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_60 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_66 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_58 apart128_ee_59

theorem apart128_ee_61 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_81 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_62 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_88 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_63 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_91 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_64 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_92 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_65 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_93 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_66 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_94 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_67 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_94 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_68 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_94 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_66 apart128_ee_67

theorem apart128_ee_69 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_95 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_65 apart128_ee_68

theorem apart128_ee_70 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_96 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_64 apart128_ee_69

theorem apart128_ee_71 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_97 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_63 apart128_ee_70

theorem apart128_ee_72 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_98 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_62 apart128_ee_71

theorem apart128_ee_73 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_99 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_61 apart128_ee_72

theorem apart128_ee_74 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_114 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_75 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_117 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_76 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_118 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_77 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_119 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_78 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_119 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_79 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_119 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_77 apart128_ee_78

theorem apart128_ee_80 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_120 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_76 apart128_ee_79

theorem apart128_ee_81 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_121 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_75 apart128_ee_80

theorem apart128_ee_82 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_124 edgeNode_541=true :=
  by decide +kernel

theorem apart128_ee_83 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_125 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_84 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_125 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_85 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_125 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_83 apart128_ee_84

theorem apart128_ee_86 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_126 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_87 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_126 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_88 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_126 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_86 apart128_ee_87

theorem apart128_ee_89 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_127 edgeNode_405=true :=
  by decide +kernel

theorem apart128_ee_90 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_127 edgeNode_540=true :=
  by decide +kernel

theorem apart128_ee_91 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_127 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_89 apart128_ee_90

theorem apart128_ee_92 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_128 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_88 apart128_ee_91

theorem apart128_ee_93 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_129 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_85 apart128_ee_92

theorem apart128_ee_94 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_130 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_82 apart128_ee_93

theorem apart128_ee_95 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_131 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_81 apart128_ee_94

theorem apart128_ee_96 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_132 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_74 apart128_ee_95

theorem apart128_ee_97 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_133 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_73 apart128_ee_96

theorem apart128_ee_98 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_134 edgeNode_541=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_60 apart128_ee_97

theorem apart128_ee_99 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_141 edgeNode_541=true :=
  by decide +kernel

end PlanarHom.ColoringTestMacroCoordinates
