import PlanarHom.ColoringFanMacroSpatialCheck128_129
noncomputable section
namespace PlanarHom.ColoringFanMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ee_13000 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4331 edgeNode_4412=true :=
  by decide +kernel

theorem self128_13001 : edgeNode_4413.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_12995 self128_12999 apart128_ee_13000

theorem self128_13002 : edgeNode_4452.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_13003 : edgeNode_4493.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_13004 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4452 edgeNode_4493=true :=
  by decide +kernel

theorem self128_13005 : edgeNode_4494.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13002 self128_13003 apart128_ee_13004

theorem self128_13006 : edgeNode_4533.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_13007 : edgeNode_4574.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_13008 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4533 edgeNode_4574=true :=
  by decide +kernel

theorem self128_13009 : edgeNode_4575.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13006 self128_13007 apart128_ee_13008

theorem apart128_ee_13010 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4494 edgeNode_4575=true :=
  by decide +kernel

theorem self128_13011 : edgeNode_4576.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13005 self128_13009 apart128_ee_13010

theorem apart128_ee_13012 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4331 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13013 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4412 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13014 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4413 edgeNode_4576=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13012 apart128_ee_13013

theorem self128_13015 : edgeNode_4577.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_13001 self128_13011 apart128_ee_13014

theorem apart128_ee_13016 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4004 edgeNode_4577=true :=
  by decide +kernel

theorem apart128_ee_13017 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4013 edgeNode_4577=true :=
  by decide +kernel

theorem apart128_ee_13018 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4016 edgeNode_4577=true :=
  by decide +kernel

theorem apart128_ee_13019 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4017 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13020 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4017 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13021 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4017 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13019 apart128_ee_13020

theorem apart128_ee_13022 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4018 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13023 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4018 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13024 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4018 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13022 apart128_ee_13023

theorem apart128_ee_13025 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4019 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13026 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4019 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13027 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4019 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13025 apart128_ee_13026

theorem apart128_ee_13028 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4020 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13024 apart128_ee_13027

theorem apart128_ee_13029 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4021 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13021 apart128_ee_13028

theorem apart128_ee_13030 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4022 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13018 apart128_ee_13029

theorem apart128_ee_13031 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4023 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13017 apart128_ee_13030

theorem apart128_ee_13032 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4026 edgeNode_4577=true :=
  by decide +kernel

theorem apart128_ee_13033 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4027 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13034 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4027 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13035 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4027 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13033 apart128_ee_13034

theorem apart128_ee_13036 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4030 edgeNode_4577=true :=
  by decide +kernel

theorem apart128_ee_13037 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4031 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13035 apart128_ee_13036

theorem apart128_ee_13038 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4032 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13032 apart128_ee_13037

theorem apart128_ee_13039 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4033 edgeNode_4577=true :=
  by decide +kernel

theorem apart128_ee_13040 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4034 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13041 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4034 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13042 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4034 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13040 apart128_ee_13041

theorem apart128_ee_13043 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4035 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13039 apart128_ee_13042

theorem apart128_ee_13044 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4036 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13045 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4036 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13046 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4036 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13044 apart128_ee_13045

theorem apart128_ee_13047 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4037 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13048 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4037 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13049 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4037 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13047 apart128_ee_13048

theorem apart128_ee_13050 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4038 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13051 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4038 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13052 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4038 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13050 apart128_ee_13051

theorem apart128_ee_13053 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4039 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13049 apart128_ee_13052

theorem apart128_ee_13054 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4040 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13046 apart128_ee_13053

theorem apart128_ee_13055 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4041 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13043 apart128_ee_13054

theorem apart128_ee_13056 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4042 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13038 apart128_ee_13055

theorem apart128_ee_13057 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4043 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13031 apart128_ee_13056

theorem apart128_ee_13058 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4044 edgeNode_4577=true :=
  by decide +kernel

theorem apart128_ee_13059 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4045 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13060 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4045 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13061 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4045 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13059 apart128_ee_13060

theorem apart128_ee_13062 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4046 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13058 apart128_ee_13061

theorem apart128_ee_13063 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4047 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13064 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4047 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13065 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4047 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13063 apart128_ee_13064

theorem apart128_ee_13066 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4048 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13067 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4048 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13068 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4048 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13066 apart128_ee_13067

theorem apart128_ee_13069 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4049 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13070 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4049 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13071 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4049 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13069 apart128_ee_13070

theorem apart128_ee_13072 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4050 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13068 apart128_ee_13071

theorem apart128_ee_13073 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4051 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13065 apart128_ee_13072

theorem apart128_ee_13074 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4052 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13062 apart128_ee_13073

theorem apart128_ee_13075 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4053 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13076 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4053 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13077 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4053 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13075 apart128_ee_13076

theorem apart128_ee_13078 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4054 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13079 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4054 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13080 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4054 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13078 apart128_ee_13079

theorem apart128_ee_13081 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4055 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13077 apart128_ee_13080

theorem apart128_ee_13082 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4056 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13083 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4056 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13084 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4056 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13082 apart128_ee_13083

theorem apart128_ee_13085 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4057 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13086 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4057 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13087 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4057 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13085 apart128_ee_13086

theorem apart128_ee_13088 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4058 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13089 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4058 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13090 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4058 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13088 apart128_ee_13089

theorem apart128_ee_13091 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4059 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13087 apart128_ee_13090

theorem apart128_ee_13092 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4060 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13084 apart128_ee_13091

theorem apart128_ee_13093 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4061 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13081 apart128_ee_13092

theorem apart128_ee_13094 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4062 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_13074 apart128_ee_13093

theorem apart128_ee_13095 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4063 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13096 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4063 edgeNode_4576=true :=
  by decide +kernel

theorem apart128_ee_13097 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4063 edgeNode_4577=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_13095 apart128_ee_13096

theorem apart128_ee_13098 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4064 edgeNode_4413=true :=
  by decide +kernel

theorem apart128_ee_13099 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_4064 edgeNode_4576=true :=
  by decide +kernel

end PlanarHom.ColoringFanMacroCoordinates
