import PlanarHom.ColoringFanMacroSpatialData
noncomputable section
namespace PlanarHom.ColoringFanMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem self128_0 : edgeNode_38.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1 : edgeNode_77.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_2 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_38 edgeNode_77=true :=
  by decide +kernel

theorem self128_3 : edgeNode_78.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_0 self128_1 apart128_ee_2

theorem self128_4 : edgeNode_117.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_5 : edgeNode_158.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_6 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_117 edgeNode_158=true :=
  by decide +kernel

theorem self128_7 : edgeNode_159.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_4 self128_5 apart128_ee_6

theorem apart128_ee_8 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_78 edgeNode_159=true :=
  by decide +kernel

theorem self128_9 : edgeNode_160.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_3 self128_7 apart128_ee_8

theorem self128_10 : edgeNode_199.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_11 : edgeNode_240.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_12 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_199 edgeNode_240=true :=
  by decide +kernel

theorem self128_13 : edgeNode_241.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_10 self128_11 apart128_ee_12

theorem self128_14 : edgeNode_280.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_15 : edgeNode_321.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_16 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_280 edgeNode_321=true :=
  by decide +kernel

theorem self128_17 : edgeNode_322.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_14 self128_15 apart128_ee_16

theorem apart128_ee_18 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_241 edgeNode_322=true :=
  by decide +kernel

theorem self128_19 : edgeNode_323.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13 self128_17 apart128_ee_18

theorem apart128_ee_20 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_78 edgeNode_323=true :=
  by decide +kernel

theorem apart128_ee_21 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_159 edgeNode_323=true :=
  by decide +kernel

theorem apart128_ee_22 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_160 edgeNode_323=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_20 apart128_ee_21

theorem self128_23 : edgeNode_324.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_9 self128_19 apart128_ee_22

theorem self128_24 : edgeNode_363.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_25 : edgeNode_404.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_26 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_363 edgeNode_404=true :=
  by decide +kernel

theorem self128_27 : edgeNode_405.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_24 self128_25 apart128_ee_26

theorem self128_28 : edgeNode_444.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_29 : edgeNode_485.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_30 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_444 edgeNode_485=true :=
  by decide +kernel

theorem self128_31 : edgeNode_486.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_28 self128_29 apart128_ee_30

theorem apart128_ee_32 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_405 edgeNode_486=true :=
  by decide +kernel

theorem self128_33 : edgeNode_487.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_27 self128_31 apart128_ee_32

theorem self128_34 : edgeNode_526.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_35 : edgeNode_567.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_36 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_526 edgeNode_567=true :=
  by decide +kernel

theorem self128_37 : edgeNode_568.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_34 self128_35 apart128_ee_36

theorem self128_38 : edgeNode_607.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_39 : edgeNode_648.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_40 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_607 edgeNode_648=true :=
  by decide +kernel

theorem self128_41 : edgeNode_649.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_38 self128_39 apart128_ee_40

theorem apart128_ee_42 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_568 edgeNode_649=true :=
  by decide +kernel

theorem self128_43 : edgeNode_650.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_37 self128_41 apart128_ee_42

theorem apart128_ee_44 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_405 edgeNode_650=true :=
  by decide +kernel

theorem apart128_ee_45 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_486 edgeNode_650=true :=
  by decide +kernel

theorem apart128_ee_46 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_487 edgeNode_650=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_44 apart128_ee_45

theorem self128_47 : edgeNode_651.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_33 self128_43 apart128_ee_46

theorem apart128_ee_48 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_18 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_49 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_27 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_50 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_28 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_51 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_29 edgeNode_487=true :=
  by decide +kernel

theorem apart128_ee_52 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_29 edgeNode_650=true :=
  by decide +kernel

theorem apart128_ee_53 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_29 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_51 apart128_ee_52

theorem apart128_ee_54 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_30 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_50 apart128_ee_53

theorem apart128_ee_55 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_35 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_56 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_36 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_54 apart128_ee_55

theorem apart128_ee_57 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_37 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_49 apart128_ee_56

theorem apart128_ee_58 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_38 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_48 apart128_ee_57

theorem apart128_ee_59 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_77 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_60 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_78 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_58 apart128_ee_59

theorem apart128_ee_61 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_117 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_62 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_126 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_63 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_129 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_64 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_130 edgeNode_487=true :=
  by decide +kernel

theorem apart128_ee_65 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_130 edgeNode_650=true :=
  by decide +kernel

theorem apart128_ee_66 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_130 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_64 apart128_ee_65

theorem apart128_ee_67 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_133 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_68 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_134 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_66 apart128_ee_67

theorem apart128_ee_69 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_135 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_63 apart128_ee_68

theorem apart128_ee_70 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_136 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_62 apart128_ee_69

theorem apart128_ee_71 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_137 edgeNode_487=true :=
  by decide +kernel

theorem apart128_ee_72 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_137 edgeNode_650=true :=
  by decide +kernel

theorem apart128_ee_73 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_137 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_71 apart128_ee_72

theorem apart128_ee_74 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_138 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_75 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_139 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_73 apart128_ee_74

theorem apart128_ee_76 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_144 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_77 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_145 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_75 apart128_ee_76

theorem apart128_ee_78 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_156 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_79 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_157 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_77 apart128_ee_78

theorem apart128_ee_80 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_158 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_70 apart128_ee_79

theorem apart128_ee_81 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_159 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_61 apart128_ee_80

theorem apart128_ee_82 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_160 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_60 apart128_ee_81

theorem apart128_ee_83 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_161 edgeNode_487=true :=
  by decide +kernel

theorem apart128_ee_84 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_161 edgeNode_650=true :=
  by decide +kernel

theorem apart128_ee_85 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_161 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_83 apart128_ee_84

theorem apart128_ee_86 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_162 edgeNode_651=true :=
  by decide +kernel

theorem apart128_ee_87 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_163 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_85 apart128_ee_86

theorem apart128_ee_88 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_164 edgeNode_487=true :=
  by decide +kernel

theorem apart128_ee_89 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_164 edgeNode_650=true :=
  by decide +kernel

theorem apart128_ee_90 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_164 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_88 apart128_ee_89

theorem apart128_ee_91 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_165 edgeNode_487=true :=
  by decide +kernel

theorem apart128_ee_92 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_165 edgeNode_650=true :=
  by decide +kernel

theorem apart128_ee_93 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_165 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_91 apart128_ee_92

theorem apart128_ee_94 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_166 edgeNode_487=true :=
  by decide +kernel

theorem apart128_ee_95 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_166 edgeNode_650=true :=
  by decide +kernel

theorem apart128_ee_96 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_166 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_94 apart128_ee_95

theorem apart128_ee_97 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_167 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_93 apart128_ee_96

theorem apart128_ee_98 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_168 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_90 apart128_ee_97

theorem apart128_ee_99 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_169 edgeNode_651=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_87 apart128_ee_98

end PlanarHom.ColoringFanMacroCoordinates
