import PlanarHom.ColoringCrossMacroSpatialData
noncomputable section
namespace PlanarHom.ColoringCrossMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem self128_0 : edgeNode_46.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1 : edgeNode_95.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_2 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_46 edgeNode_95=true :=
  by decide +kernel

theorem self128_3 : edgeNode_96.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_0 self128_1 apart128_ee_2

theorem self128_4 : edgeNode_143.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_5 : edgeNode_192.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_6 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_143 edgeNode_192=true :=
  by decide +kernel

theorem self128_7 : edgeNode_193.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_4 self128_5 apart128_ee_6

theorem apart128_ee_8 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_96 edgeNode_193=true :=
  by decide +kernel

theorem self128_9 : edgeNode_194.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_3 self128_7 apart128_ee_8

theorem self128_10 : edgeNode_241.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_11 : edgeNode_290.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_12 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_241 edgeNode_290=true :=
  by decide +kernel

theorem self128_13 : edgeNode_291.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_10 self128_11 apart128_ee_12

theorem self128_14 : edgeNode_340.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_15 : edgeNode_389.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_16 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_340 edgeNode_389=true :=
  by decide +kernel

theorem self128_17 : edgeNode_390.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_14 self128_15 apart128_ee_16

theorem apart128_ee_18 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_291 edgeNode_390=true :=
  by decide +kernel

theorem self128_19 : edgeNode_391.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13 self128_17 apart128_ee_18

theorem apart128_ee_20 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_46 edgeNode_391=true :=
  by decide +kernel

theorem apart128_ee_21 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_95 edgeNode_391=true :=
  by decide +kernel

theorem apart128_ee_22 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_96 edgeNode_391=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_20 apart128_ee_21

theorem apart128_ee_23 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_143 edgeNode_391=true :=
  by decide +kernel

theorem apart128_ee_24 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_192 edgeNode_391=true :=
  by decide +kernel

theorem apart128_ee_25 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_193 edgeNode_391=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_23 apart128_ee_24

theorem apart128_ee_26 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_194 edgeNode_391=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_22 apart128_ee_25

theorem self128_27 : edgeNode_392.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_9 self128_19 apart128_ee_26

theorem self128_28 : edgeNode_439.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_29 : edgeNode_488.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_30 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_439 edgeNode_488=true :=
  by decide +kernel

theorem self128_31 : edgeNode_489.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_28 self128_29 apart128_ee_30

theorem self128_32 : edgeNode_536.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_33 : edgeNode_585.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_34 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_536 edgeNode_585=true :=
  by decide +kernel

theorem self128_35 : edgeNode_586.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_32 self128_33 apart128_ee_34

theorem apart128_ee_36 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_489 edgeNode_586=true :=
  by decide +kernel

theorem self128_37 : edgeNode_587.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_31 self128_35 apart128_ee_36

theorem self128_38 : edgeNode_634.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_39 : edgeNode_683.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_40 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_634 edgeNode_683=true :=
  by decide +kernel

theorem self128_41 : edgeNode_684.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_38 self128_39 apart128_ee_40

theorem self128_42 : edgeNode_733.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_43 : edgeNode_782.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_44 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_733 edgeNode_782=true :=
  by decide +kernel

theorem self128_45 : edgeNode_783.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_42 self128_43 apart128_ee_44

theorem apart128_ee_46 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_684 edgeNode_783=true :=
  by decide +kernel

theorem self128_47 : edgeNode_784.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_41 self128_45 apart128_ee_46

theorem apart128_ee_48 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_439 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_49 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_488 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_50 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_489 edgeNode_784=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_48 apart128_ee_49

theorem apart128_ee_51 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_536 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_52 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_585 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_53 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_586 edgeNode_784=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_51 apart128_ee_52

theorem apart128_ee_54 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_587 edgeNode_784=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_50 apart128_ee_53

theorem self128_55 : edgeNode_785.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_37 self128_47 apart128_ee_54

theorem apart128_ee_56 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_46 edgeNode_785=true :=
  by decide +kernel

theorem apart128_ee_57 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_69 edgeNode_785=true :=
  by decide +kernel

theorem apart128_ee_58 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_80 edgeNode_785=true :=
  by decide +kernel

theorem apart128_ee_59 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_81 edgeNode_785=true :=
  by decide +kernel

theorem apart128_ee_60 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_82 edgeNode_785=true :=
  by decide +kernel

theorem apart128_ee_61 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_83 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_62 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_83 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_63 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_83 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_61 apart128_ee_62

theorem apart128_ee_64 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_84 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_60 apart128_ee_63

theorem apart128_ee_65 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_85 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_59 apart128_ee_64

theorem apart128_ee_66 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_86 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_67 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_86 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_68 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_86 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_66 apart128_ee_67

theorem apart128_ee_69 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_87 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_70 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_87 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_71 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_87 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_69 apart128_ee_70

theorem apart128_ee_72 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_88 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_68 apart128_ee_71

theorem apart128_ee_73 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_89 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_74 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_89 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_75 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_89 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_73 apart128_ee_74

theorem apart128_ee_76 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_90 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_77 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_90 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_78 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_90 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_76 apart128_ee_77

theorem apart128_ee_79 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_91 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_75 apart128_ee_78

theorem apart128_ee_80 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_92 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_72 apart128_ee_79

theorem apart128_ee_81 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_93 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_65 apart128_ee_80

theorem apart128_ee_82 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_94 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_58 apart128_ee_81

theorem apart128_ee_83 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_95 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_57 apart128_ee_82

theorem apart128_ee_84 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_96 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_56 apart128_ee_83

theorem apart128_ee_85 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_119 edgeNode_785=true :=
  by decide +kernel

theorem apart128_ee_86 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_120 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_87 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_120 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_88 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_120 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_86 apart128_ee_87

theorem apart128_ee_89 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_121 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_90 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_121 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_91 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_121 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_89 apart128_ee_90

theorem apart128_ee_92 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_122 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_93 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_122 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_94 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_122 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_92 apart128_ee_93

theorem apart128_ee_95 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_123 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_91 apart128_ee_94

theorem apart128_ee_96 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_124 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_88 apart128_ee_95

theorem apart128_ee_97 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_125 edgeNode_587=true :=
  by decide +kernel

theorem apart128_ee_98 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_125 edgeNode_784=true :=
  by decide +kernel

theorem apart128_ee_99 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_125 edgeNode_785=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_97 apart128_ee_98

end PlanarHom.ColoringCrossMacroCoordinates
