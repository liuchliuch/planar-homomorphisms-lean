import PlanarHom.ColoringCrossMacroSpatialCheck128_9
noncomputable section
namespace PlanarHom.ColoringCrossMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ee_1000 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1671 edgeNode_1768=true :=
  by decide +kernel

theorem self128_1001 : edgeNode_1769.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_995 self128_999 apart128_ee_1000

theorem self128_1002 : edgeNode_1816.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1003 : edgeNode_1865.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1004 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1816 edgeNode_1865=true :=
  by decide +kernel

theorem self128_1005 : edgeNode_1866.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1002 self128_1003 apart128_ee_1004

theorem self128_1006 : edgeNode_1915.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1007 : edgeNode_1964.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1008 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1915 edgeNode_1964=true :=
  by decide +kernel

theorem self128_1009 : edgeNode_1965.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1006 self128_1007 apart128_ee_1008

theorem apart128_ee_1010 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1866 edgeNode_1965=true :=
  by decide +kernel

theorem self128_1011 : edgeNode_1966.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1005 self128_1009 apart128_ee_1010

theorem apart128_ee_1012 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1621 edgeNode_1966=true :=
  by decide +kernel

theorem apart128_ee_1013 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1670 edgeNode_1966=true :=
  by decide +kernel

theorem apart128_ee_1014 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1671 edgeNode_1966=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1012 apart128_ee_1013

theorem apart128_ee_1015 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1718 edgeNode_1966=true :=
  by decide +kernel

theorem apart128_ee_1016 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1767 edgeNode_1966=true :=
  by decide +kernel

theorem apart128_ee_1017 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1768 edgeNode_1966=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1015 apart128_ee_1016

theorem apart128_ee_1018 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1769 edgeNode_1966=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1014 apart128_ee_1017

theorem self128_1019 : edgeNode_1967.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1001 self128_1011 apart128_ee_1018

theorem self128_1020 : edgeNode_2014.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1021 : edgeNode_2063.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1022 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2014 edgeNode_2063=true :=
  by decide +kernel

theorem self128_1023 : edgeNode_2064.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1020 self128_1021 apart128_ee_1022

theorem self128_1024 : edgeNode_2111.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1025 : edgeNode_2160.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1026 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2111 edgeNode_2160=true :=
  by decide +kernel

theorem self128_1027 : edgeNode_2161.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1024 self128_1025 apart128_ee_1026

theorem apart128_ee_1028 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2064 edgeNode_2161=true :=
  by decide +kernel

theorem self128_1029 : edgeNode_2162.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1023 self128_1027 apart128_ee_1028

theorem self128_1030 : edgeNode_2209.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1031 : edgeNode_2258.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1032 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2209 edgeNode_2258=true :=
  by decide +kernel

theorem self128_1033 : edgeNode_2259.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1030 self128_1031 apart128_ee_1032

theorem self128_1034 : edgeNode_2308.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1035 : edgeNode_2357.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1036 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2308 edgeNode_2357=true :=
  by decide +kernel

theorem self128_1037 : edgeNode_2358.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1034 self128_1035 apart128_ee_1036

theorem apart128_ee_1038 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2259 edgeNode_2358=true :=
  by decide +kernel

theorem self128_1039 : edgeNode_2359.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1033 self128_1037 apart128_ee_1038

theorem apart128_ee_1040 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2014 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1041 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2063 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1042 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2064 edgeNode_2359=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1040 apart128_ee_1041

theorem apart128_ee_1043 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2111 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1044 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2160 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1045 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2161 edgeNode_2359=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1043 apart128_ee_1044

theorem apart128_ee_1046 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_2162 edgeNode_2359=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1042 apart128_ee_1045

theorem self128_1047 : edgeNode_2360.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1029 self128_1039 apart128_ee_1046

theorem apart128_ee_1048 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1769 edgeNode_2360=true :=
  by decide +kernel

theorem apart128_ee_1049 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1780 edgeNode_2360=true :=
  by decide +kernel

theorem apart128_ee_1050 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1781 edgeNode_2360=true :=
  by decide +kernel

theorem apart128_ee_1051 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1782 edgeNode_2162=true :=
  by decide +kernel

theorem apart128_ee_1052 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1782 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1053 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1782 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1051 apart128_ee_1052

theorem apart128_ee_1054 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1783 edgeNode_2162=true :=
  by decide +kernel

theorem apart128_ee_1055 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1783 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1056 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1783 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1054 apart128_ee_1055

theorem apart128_ee_1057 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1784 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1053 apart128_ee_1056

theorem apart128_ee_1058 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1785 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1050 apart128_ee_1057

theorem apart128_ee_1059 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1786 edgeNode_2360=true :=
  by decide +kernel

theorem apart128_ee_1060 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1787 edgeNode_2162=true :=
  by decide +kernel

theorem apart128_ee_1061 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1787 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1062 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1787 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1060 apart128_ee_1061

theorem apart128_ee_1063 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1788 edgeNode_2360=true :=
  by decide +kernel

theorem apart128_ee_1064 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1789 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1062 apart128_ee_1063

theorem apart128_ee_1065 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1790 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1059 apart128_ee_1064

theorem apart128_ee_1066 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1791 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1058 apart128_ee_1065

theorem apart128_ee_1067 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1792 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1049 apart128_ee_1066

theorem apart128_ee_1068 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1793 edgeNode_2162=true :=
  by decide +kernel

theorem apart128_ee_1069 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1793 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1070 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1793 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1068 apart128_ee_1069

theorem apart128_ee_1071 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1794 edgeNode_2162=true :=
  by decide +kernel

theorem apart128_ee_1072 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1794 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1073 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1794 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1071 apart128_ee_1072

theorem apart128_ee_1074 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1795 edgeNode_2162=true :=
  by decide +kernel

theorem apart128_ee_1075 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1795 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1076 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1795 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1074 apart128_ee_1075

theorem apart128_ee_1077 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1796 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1073 apart128_ee_1076

theorem apart128_ee_1078 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1797 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1070 apart128_ee_1077

theorem apart128_ee_1079 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1798 edgeNode_2162=true :=
  by decide +kernel

theorem apart128_ee_1080 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1798 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1081 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1798 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1079 apart128_ee_1080

theorem apart128_ee_1082 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1799 edgeNode_2162=true :=
  by decide +kernel

theorem apart128_ee_1083 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1799 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1084 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1799 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1082 apart128_ee_1083

theorem apart128_ee_1085 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1800 edgeNode_2162=true :=
  by decide +kernel

theorem apart128_ee_1086 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1800 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1087 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1800 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1085 apart128_ee_1086

theorem apart128_ee_1088 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1801 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1084 apart128_ee_1087

theorem apart128_ee_1089 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1802 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1081 apart128_ee_1088

theorem apart128_ee_1090 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1803 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1078 apart128_ee_1089

theorem apart128_ee_1091 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1804 edgeNode_2162=true :=
  by decide +kernel

theorem apart128_ee_1092 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1804 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1093 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1804 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1091 apart128_ee_1092

theorem apart128_ee_1094 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1805 edgeNode_2162=true :=
  by decide +kernel

theorem apart128_ee_1095 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1805 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1096 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1805 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1094 apart128_ee_1095

theorem apart128_ee_1097 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1806 edgeNode_2162=true :=
  by decide +kernel

theorem apart128_ee_1098 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1806 edgeNode_2359=true :=
  by decide +kernel

theorem apart128_ee_1099 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1806 edgeNode_2360=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1097 apart128_ee_1098

end PlanarHom.ColoringCrossMacroCoordinates
