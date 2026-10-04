import PlanarHom.ColoringWireMacroSpatialData
noncomputable section
namespace PlanarHom.ColoringWireMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem self128_0 : edgeNode_38.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1 : edgeNode_79.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_2 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_38 edgeNode_79=true :=
  by decide +kernel

theorem self128_3 : edgeNode_80.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_0 self128_1 apart128_ee_2

theorem self128_4 : edgeNode_119.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_5 : edgeNode_160.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_6 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_119 edgeNode_160=true :=
  by decide +kernel

theorem self128_7 : edgeNode_161.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_4 self128_5 apart128_ee_6

theorem apart128_ee_8 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_80 edgeNode_161=true :=
  by decide +kernel

theorem self128_9 : edgeNode_162.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_3 self128_7 apart128_ee_8

theorem self128_10 : edgeNode_201.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_11 : edgeNode_242.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_12 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_201 edgeNode_242=true :=
  by decide +kernel

theorem self128_13 : edgeNode_243.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_10 self128_11 apart128_ee_12

theorem self128_14 : edgeNode_282.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_15 : edgeNode_323.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_16 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_282 edgeNode_323=true :=
  by decide +kernel

theorem self128_17 : edgeNode_324.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_14 self128_15 apart128_ee_16

theorem apart128_ee_18 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_243 edgeNode_324=true :=
  by decide +kernel

theorem self128_19 : edgeNode_325.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13 self128_17 apart128_ee_18

theorem apart128_ee_20 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_80 edgeNode_325=true :=
  by decide +kernel

theorem apart128_ee_21 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_161 edgeNode_325=true :=
  by decide +kernel

theorem apart128_ee_22 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_162 edgeNode_325=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_20 apart128_ee_21

theorem self128_23 : edgeNode_326.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_9 self128_19 apart128_ee_22

theorem self128_24 : edgeNode_365.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_25 : edgeNode_406.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_26 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_365 edgeNode_406=true :=
  by decide +kernel

theorem self128_27 : edgeNode_407.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_24 self128_25 apart128_ee_26

theorem self128_28 : edgeNode_446.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_29 : edgeNode_487.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_30 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_446 edgeNode_487=true :=
  by decide +kernel

theorem self128_31 : edgeNode_488.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_28 self128_29 apart128_ee_30

theorem apart128_ee_32 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_407 edgeNode_488=true :=
  by decide +kernel

theorem self128_33 : edgeNode_489.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_27 self128_31 apart128_ee_32

theorem self128_34 : edgeNode_528.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_35 : edgeNode_569.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_36 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_528 edgeNode_569=true :=
  by decide +kernel

theorem self128_37 : edgeNode_570.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_34 self128_35 apart128_ee_36

theorem self128_38 : edgeNode_609.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_39 : edgeNode_650.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_40 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_609 edgeNode_650=true :=
  by decide +kernel

theorem self128_41 : edgeNode_651.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_38 self128_39 apart128_ee_40

theorem apart128_ee_42 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_570 edgeNode_651=true :=
  by decide +kernel

theorem self128_43 : edgeNode_652.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_37 self128_41 apart128_ee_42

theorem apart128_ee_44 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_407 edgeNode_652=true :=
  by decide +kernel

theorem apart128_ee_45 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_488 edgeNode_652=true :=
  by decide +kernel

theorem apart128_ee_46 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_489 edgeNode_652=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_44 apart128_ee_45

theorem self128_47 : edgeNode_653.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_33 self128_43 apart128_ee_46

theorem apart128_ee_48 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_80 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_49 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_119 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_50 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_138 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_51 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_141 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_52 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_142 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_53 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_143 edgeNode_489=true :=
  by decide +kernel

theorem apart128_ee_54 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_143 edgeNode_652=true :=
  by decide +kernel

theorem apart128_ee_55 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_143 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_53 apart128_ee_54

theorem apart128_ee_56 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_144 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_57 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_145 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_55 apart128_ee_56

theorem apart128_ee_58 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_146 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_52 apart128_ee_57

theorem apart128_ee_59 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_147 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_51 apart128_ee_58

theorem apart128_ee_60 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_158 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_61 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_159 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_59 apart128_ee_60

theorem apart128_ee_62 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_160 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_50 apart128_ee_61

theorem apart128_ee_63 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_161 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_49 apart128_ee_62

theorem apart128_ee_64 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_162 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_48 apart128_ee_63

theorem apart128_ee_65 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_181 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_66 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_184 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_67 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_185 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_68 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_186 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_69 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_187 edgeNode_489=true :=
  by decide +kernel

theorem apart128_ee_70 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_187 edgeNode_652=true :=
  by decide +kernel

theorem apart128_ee_71 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_187 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_69 apart128_ee_70

theorem apart128_ee_72 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_188 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_68 apart128_ee_71

theorem apart128_ee_73 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_189 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_67 apart128_ee_72

theorem apart128_ee_74 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_190 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_66 apart128_ee_73

theorem apart128_ee_75 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_191 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_76 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_192 edgeNode_489=true :=
  by decide +kernel

theorem apart128_ee_77 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_192 edgeNode_652=true :=
  by decide +kernel

theorem apart128_ee_78 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_192 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_76 apart128_ee_77

theorem apart128_ee_79 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_193 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_75 apart128_ee_78

theorem apart128_ee_80 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_198 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_81 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_199 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_79 apart128_ee_80

theorem apart128_ee_82 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_200 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_74 apart128_ee_81

theorem apart128_ee_83 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_201 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_65 apart128_ee_82

theorem apart128_ee_84 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_202 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_85 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_203 edgeNode_489=true :=
  by decide +kernel

theorem apart128_ee_86 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_203 edgeNode_652=true :=
  by decide +kernel

theorem apart128_ee_87 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_203 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_85 apart128_ee_86

theorem apart128_ee_88 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_204 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_84 apart128_ee_87

theorem apart128_ee_89 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_205 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_90 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_206 edgeNode_489=true :=
  by decide +kernel

theorem apart128_ee_91 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_206 edgeNode_652=true :=
  by decide +kernel

theorem apart128_ee_92 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_206 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_90 apart128_ee_91

theorem apart128_ee_93 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_207 edgeNode_653=true :=
  by decide +kernel

theorem apart128_ee_94 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_208 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_92 apart128_ee_93

theorem apart128_ee_95 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_209 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_89 apart128_ee_94

theorem apart128_ee_96 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_210 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_88 apart128_ee_95

theorem apart128_ee_97 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_211 edgeNode_489=true :=
  by decide +kernel

theorem apart128_ee_98 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_211 edgeNode_652=true :=
  by decide +kernel

theorem apart128_ee_99 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_211 edgeNode_653=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_97 apart128_ee_98

end PlanarHom.ColoringWireMacroCoordinates
