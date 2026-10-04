import PlanarHom.ColoringCrossMacroSpatialCheck128_49
noncomputable section
namespace PlanarHom.ColoringCrossMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ee_5000 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5108 edgeNode_5511=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_4996 apart128_ee_4999

theorem apart128_ee_5001 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5109 edgeNode_5313=true :=
  by decide +kernel

theorem apart128_ee_5002 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5109 edgeNode_5510=true :=
  by decide +kernel

theorem apart128_ee_5003 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5109 edgeNode_5511=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_5001 apart128_ee_5002

theorem apart128_ee_5004 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5110 edgeNode_5313=true :=
  by decide +kernel

theorem apart128_ee_5005 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5110 edgeNode_5510=true :=
  by decide +kernel

theorem apart128_ee_5006 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5110 edgeNode_5511=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_5004 apart128_ee_5005

theorem apart128_ee_5007 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5111 edgeNode_5511=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_5003 apart128_ee_5006

theorem apart128_ee_5008 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5112 edgeNode_5511=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_5000 apart128_ee_5007

theorem apart128_ee_5009 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5113 edgeNode_5511=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_4995 apart128_ee_5008

theorem apart128_ee_5010 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5114 edgeNode_5511=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_4986 apart128_ee_5009

theorem apart128_ee_5011 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5115 edgeNode_5511=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_4985 apart128_ee_5010

theorem apart128_ee_5012 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5116 edgeNode_5511=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_4960 apart128_ee_5011

theorem apart128_ee_5013 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5117 edgeNode_5511=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_4959 apart128_ee_5012

theorem apart128_ee_5014 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5118 edgeNode_5511=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_4958 apart128_ee_5013

theorem self128_5015 : edgeNode_5512.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_4929 self128_4957 apart128_ee_5014

theorem self128_5016 : edgeNode_5559.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_5017 : edgeNode_5608.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_5018 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5559 edgeNode_5608=true :=
  by decide +kernel

theorem self128_5019 : edgeNode_5609.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5016 self128_5017 apart128_ee_5018

theorem self128_5020 : edgeNode_5656.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_5021 : edgeNode_5705.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_5022 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5656 edgeNode_5705=true :=
  by decide +kernel

theorem self128_5023 : edgeNode_5706.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5020 self128_5021 apart128_ee_5022

theorem apart128_ee_5024 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5609 edgeNode_5706=true :=
  by decide +kernel

theorem self128_5025 : edgeNode_5707.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5019 self128_5023 apart128_ee_5024

theorem self128_5026 : edgeNode_5754.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_5027 : edgeNode_5803.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_5028 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5754 edgeNode_5803=true :=
  by decide +kernel

theorem self128_5029 : edgeNode_5804.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5026 self128_5027 apart128_ee_5028

theorem self128_5030 : edgeNode_5853.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_5031 : edgeNode_5902.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_5032 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5853 edgeNode_5902=true :=
  by decide +kernel

theorem self128_5033 : edgeNode_5903.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5030 self128_5031 apart128_ee_5032

theorem apart128_ee_5034 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5804 edgeNode_5903=true :=
  by decide +kernel

theorem self128_5035 : edgeNode_5904.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5029 self128_5033 apart128_ee_5034

theorem apart128_ee_5036 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5559 edgeNode_5904=true :=
  by decide +kernel

theorem apart128_ee_5037 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5608 edgeNode_5904=true :=
  by decide +kernel

theorem apart128_ee_5038 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5609 edgeNode_5904=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_5036 apart128_ee_5037

theorem apart128_ee_5039 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5656 edgeNode_5904=true :=
  by decide +kernel

theorem apart128_ee_5040 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5705 edgeNode_5904=true :=
  by decide +kernel

theorem apart128_ee_5041 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5706 edgeNode_5904=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_5039 apart128_ee_5040

theorem apart128_ee_5042 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5707 edgeNode_5904=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_5038 apart128_ee_5041

theorem self128_5043 : edgeNode_5905.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5025 self128_5035 apart128_ee_5042

theorem self128_5044 : edgeNode_5952.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_5045 : edgeNode_6001.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_5046 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5952 edgeNode_6001=true :=
  by decide +kernel

theorem self128_5047 : edgeNode_6002.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5044 self128_5045 apart128_ee_5046

theorem self128_5048 : edgeNode_6049.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_5049 : edgeNode_6098.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_5050 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_6049 edgeNode_6098=true :=
  by decide +kernel

theorem self128_5051 : edgeNode_6099.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5048 self128_5049 apart128_ee_5050

theorem apart128_ee_5052 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_6002 edgeNode_6099=true :=
  by decide +kernel

theorem self128_5053 : edgeNode_6100.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5047 self128_5051 apart128_ee_5052

theorem self128_5054 : edgeNode_6147.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_5055 : edgeNode_6196.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_5056 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_6147 edgeNode_6196=true :=
  by decide +kernel

theorem self128_5057 : edgeNode_6197.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5054 self128_5055 apart128_ee_5056

theorem self128_5058 : edgeNode_6246.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_5059 : edgeNode_6295.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_5060 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_6246 edgeNode_6295=true :=
  by decide +kernel

theorem self128_5061 : edgeNode_6296.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5058 self128_5059 apart128_ee_5060

theorem apart128_ee_5062 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_6197 edgeNode_6296=true :=
  by decide +kernel

theorem self128_5063 : edgeNode_6297.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5057 self128_5061 apart128_ee_5062

theorem apart128_ee_5064 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5952 edgeNode_6297=true :=
  by decide +kernel

theorem apart128_ee_5065 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_6001 edgeNode_6297=true :=
  by decide +kernel

theorem apart128_ee_5066 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_6002 edgeNode_6297=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_5064 apart128_ee_5065

theorem apart128_ee_5067 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_6049 edgeNode_6297=true :=
  by decide +kernel

theorem apart128_ee_5068 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_6098 edgeNode_6297=true :=
  by decide +kernel

theorem apart128_ee_5069 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_6099 edgeNode_6297=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_5067 apart128_ee_5068

theorem apart128_ee_5070 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_6100 edgeNode_6297=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_5066 apart128_ee_5069

theorem self128_5071 : edgeNode_6298.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_5053 self128_5063 apart128_ee_5070

theorem apart128_ee_5072 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5707 edgeNode_6298=true :=
  by decide +kernel

theorem apart128_ee_5073 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5754 edgeNode_6298=true :=
  by decide +kernel

theorem apart128_ee_5074 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5777 edgeNode_6298=true :=
  by decide +kernel

theorem apart128_ee_5075 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5788 edgeNode_6298=true :=
  by decide +kernel

theorem apart128_ee_5076 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5789 edgeNode_6100=true :=
  by decide +kernel

theorem apart128_ee_5077 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5789 edgeNode_6297=true :=
  by decide +kernel

theorem apart128_ee_5078 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5789 edgeNode_6298=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_5076 apart128_ee_5077

theorem apart128_ee_5079 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5790 edgeNode_6100=true :=
  by decide +kernel

theorem apart128_ee_5080 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5790 edgeNode_6297=true :=
  by decide +kernel

theorem apart128_ee_5081 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5790 edgeNode_6298=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_5079 apart128_ee_5080

theorem apart128_ee_5082 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5791 edgeNode_6100=true :=
  by decide +kernel

theorem apart128_ee_5083 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5791 edgeNode_6297=true :=
  by decide +kernel

theorem apart128_ee_5084 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5791 edgeNode_6298=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_5082 apart128_ee_5083

theorem apart128_ee_5085 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5792 edgeNode_6298=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_5081 apart128_ee_5084

theorem apart128_ee_5086 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5793 edgeNode_6298=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_5078 apart128_ee_5085

theorem apart128_ee_5087 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5794 edgeNode_6100=true :=
  by decide +kernel

theorem apart128_ee_5088 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5794 edgeNode_6297=true :=
  by decide +kernel

theorem apart128_ee_5089 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5794 edgeNode_6298=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_5087 apart128_ee_5088

theorem apart128_ee_5090 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5795 edgeNode_6100=true :=
  by decide +kernel

theorem apart128_ee_5091 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5795 edgeNode_6297=true :=
  by decide +kernel

theorem apart128_ee_5092 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5795 edgeNode_6298=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_5090 apart128_ee_5091

theorem apart128_ee_5093 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5796 edgeNode_6298=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_5089 apart128_ee_5092

theorem apart128_ee_5094 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5797 edgeNode_6100=true :=
  by decide +kernel

theorem apart128_ee_5095 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5797 edgeNode_6297=true :=
  by decide +kernel

theorem apart128_ee_5096 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5797 edgeNode_6298=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_5094 apart128_ee_5095

theorem apart128_ee_5097 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5798 edgeNode_6100=true :=
  by decide +kernel

theorem apart128_ee_5098 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5798 edgeNode_6297=true :=
  by decide +kernel

theorem apart128_ee_5099 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_5798 edgeNode_6298=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_5097 apart128_ee_5098

end PlanarHom.ColoringCrossMacroCoordinates
