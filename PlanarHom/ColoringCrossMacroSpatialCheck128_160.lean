import PlanarHom.ColoringCrossMacroSpatialCheck128_159
noncomputable section
namespace PlanarHom.ColoringCrossMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ev_16000 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1263 vertexNode_471=true :=
  by decide +kernel

theorem apart128_ev_16001 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1263 vertexNode_630=true :=
  by decide +kernel

theorem apart128_ev_16002 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1263 vertexNode_631=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16000 apart128_ev_16001

theorem apart128_ev_16003 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1263 vertexNode_632=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_15999 apart128_ev_16002

theorem apart128_ev_16004 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1263 vertexNode_1267=true :=
  by decide +kernel

theorem apart128_ev_16005 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1263 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16003 apart128_ev_16004

theorem apart128_ev_16006 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1263 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_16007 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1263 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16005 apart128_ev_16006

theorem apart128_ev_16008 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1264 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_15998 apart128_ev_16007

theorem apart128_ev_16009 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1265 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_15989 apart128_ev_16008

theorem apart128_ev_16010 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1266 vertexNode_314=true :=
  by decide +kernel

theorem apart128_ev_16011 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1266 vertexNode_471=true :=
  by decide +kernel

theorem apart128_ev_16012 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1266 vertexNode_630=true :=
  by decide +kernel

theorem apart128_ev_16013 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1266 vertexNode_631=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16011 apart128_ev_16012

theorem apart128_ev_16014 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1266 vertexNode_632=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16010 apart128_ev_16013

theorem apart128_ev_16015 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1266 vertexNode_1267=true :=
  by decide +kernel

theorem apart128_ev_16016 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1266 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16014 apart128_ev_16015

theorem apart128_ev_16017 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1266 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_16018 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1266 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16016 apart128_ev_16017

theorem apart128_ev_16019 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1267 vertexNode_314=true :=
  by decide +kernel

theorem apart128_ev_16020 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1267 vertexNode_471=true :=
  by decide +kernel

theorem apart128_ev_16021 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1267 vertexNode_630=true :=
  by decide +kernel

theorem apart128_ev_16022 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1267 vertexNode_631=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16020 apart128_ev_16021

theorem apart128_ev_16023 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1267 vertexNode_632=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16019 apart128_ev_16022

theorem apart128_ev_16024 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1267 vertexNode_1267=true :=
  by decide +kernel

theorem apart128_ev_16025 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1267 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16023 apart128_ev_16024

theorem apart128_ev_16026 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1267 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_16027 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1267 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16025 apart128_ev_16026

theorem apart128_ev_16028 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1268 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_16018 apart128_ev_16027

theorem apart128_ev_16029 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1269 vertexNode_314=true :=
  by decide +kernel

theorem apart128_ev_16030 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1269 vertexNode_471=true :=
  by decide +kernel

theorem apart128_ev_16031 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1269 vertexNode_630=true :=
  by decide +kernel

theorem apart128_ev_16032 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1269 vertexNode_631=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16030 apart128_ev_16031

theorem apart128_ev_16033 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1269 vertexNode_632=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16029 apart128_ev_16032

theorem apart128_ev_16034 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1269 vertexNode_1267=true :=
  by decide +kernel

theorem apart128_ev_16035 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1269 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16033 apart128_ev_16034

theorem apart128_ev_16036 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1269 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_16037 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1269 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16035 apart128_ev_16036

theorem apart128_ev_16038 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1270 vertexNode_314=true :=
  by decide +kernel

theorem apart128_ev_16039 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1270 vertexNode_471=true :=
  by decide +kernel

theorem apart128_ev_16040 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1270 vertexNode_630=true :=
  by decide +kernel

theorem apart128_ev_16041 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1270 vertexNode_631=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16039 apart128_ev_16040

theorem apart128_ev_16042 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1270 vertexNode_632=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16038 apart128_ev_16041

theorem apart128_ev_16043 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1270 vertexNode_1267=true :=
  by decide +kernel

theorem apart128_ev_16044 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1270 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16042 apart128_ev_16043

theorem apart128_ev_16045 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1270 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_16046 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1270 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16044 apart128_ev_16045

theorem apart128_ev_16047 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1271 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_16037 apart128_ev_16046

theorem apart128_ev_16048 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1272 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_16028 apart128_ev_16047

theorem apart128_ev_16049 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1273 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_16009 apart128_ev_16048

theorem apart128_ev_16050 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1274 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_15980 apart128_ev_16049

theorem apart128_ev_16051 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1275 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_15921 apart128_ev_16050

theorem apart128_ev_16052 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1276 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_15802 apart128_ev_16051

theorem apart128_ev_16053 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1277 vertexNode_314=true :=
  by decide +kernel

theorem apart128_ev_16054 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1277 vertexNode_471=true :=
  by decide +kernel

theorem apart128_ev_16055 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1277 vertexNode_630=true :=
  by decide +kernel

theorem apart128_ev_16056 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1277 vertexNode_631=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16054 apart128_ev_16055

theorem apart128_ev_16057 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1277 vertexNode_632=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16053 apart128_ev_16056

theorem apart128_ev_16058 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1277 vertexNode_1267=true :=
  by decide +kernel

theorem apart128_ev_16059 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1277 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16057 apart128_ev_16058

theorem apart128_ev_16060 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1277 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_16061 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1277 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16059 apart128_ev_16060

theorem apart128_ev_16062 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1278 vertexNode_314=true :=
  by decide +kernel

theorem apart128_ev_16063 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1278 vertexNode_471=true :=
  by decide +kernel

theorem apart128_ev_16064 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1278 vertexNode_630=true :=
  by decide +kernel

theorem apart128_ev_16065 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1278 vertexNode_631=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16063 apart128_ev_16064

theorem apart128_ev_16066 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1278 vertexNode_632=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16062 apart128_ev_16065

theorem apart128_ev_16067 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1278 vertexNode_1267=true :=
  by decide +kernel

theorem apart128_ev_16068 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1278 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16066 apart128_ev_16067

theorem apart128_ev_16069 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1278 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_16070 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1278 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16068 apart128_ev_16069

theorem apart128_ev_16071 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1279 vertexNode_314=true :=
  by decide +kernel

theorem apart128_ev_16072 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1279 vertexNode_471=true :=
  by decide +kernel

theorem apart128_ev_16073 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1279 vertexNode_630=true :=
  by decide +kernel

theorem apart128_ev_16074 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1279 vertexNode_631=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16072 apart128_ev_16073

theorem apart128_ev_16075 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1279 vertexNode_632=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16071 apart128_ev_16074

theorem apart128_ev_16076 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1279 vertexNode_1267=true :=
  by decide +kernel

theorem apart128_ev_16077 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1279 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16075 apart128_ev_16076

theorem apart128_ev_16078 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1279 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_16079 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1279 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16077 apart128_ev_16078

theorem apart128_ev_16080 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1280 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_16070 apart128_ev_16079

theorem apart128_ev_16081 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1281 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_16061 apart128_ev_16080

theorem apart128_ev_16082 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1282 vertexNode_314=true :=
  by decide +kernel

theorem apart128_ev_16083 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1282 vertexNode_471=true :=
  by decide +kernel

theorem apart128_ev_16084 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1282 vertexNode_630=true :=
  by decide +kernel

theorem apart128_ev_16085 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1282 vertexNode_631=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16083 apart128_ev_16084

theorem apart128_ev_16086 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1282 vertexNode_632=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16082 apart128_ev_16085

theorem apart128_ev_16087 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1282 vertexNode_1267=true :=
  by decide +kernel

theorem apart128_ev_16088 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1282 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16086 apart128_ev_16087

theorem apart128_ev_16089 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1282 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_16090 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1282 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16088 apart128_ev_16089

theorem apart128_ev_16091 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1283 vertexNode_314=true :=
  by decide +kernel

theorem apart128_ev_16092 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1283 vertexNode_471=true :=
  by decide +kernel

theorem apart128_ev_16093 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1283 vertexNode_630=true :=
  by decide +kernel

theorem apart128_ev_16094 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1283 vertexNode_631=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16092 apart128_ev_16093

theorem apart128_ev_16095 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1283 vertexNode_632=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16091 apart128_ev_16094

theorem apart128_ev_16096 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1283 vertexNode_1267=true :=
  by decide +kernel

theorem apart128_ev_16097 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1283 vertexNode_1268=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16095 apart128_ev_16096

theorem apart128_ev_16098 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1283 vertexNode_2537=true :=
  by decide +kernel

theorem apart128_ev_16099 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_1283 vertexNode_2538=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ev_16097 apart128_ev_16098

end PlanarHom.ColoringCrossMacroCoordinates
