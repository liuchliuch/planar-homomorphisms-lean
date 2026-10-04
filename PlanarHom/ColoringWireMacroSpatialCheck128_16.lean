import PlanarHom.ColoringWireMacroSpatialCheck128_15
noncomputable section
namespace PlanarHom.ColoringWireMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem self128_1600 : edgeNode_1920.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1601 : edgeNode_1961.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1602 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1920 edgeNode_1961=true :=
  by decide +kernel

theorem self128_1603 : edgeNode_1962.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1600 self128_1601 apart128_ee_1602

theorem apart128_ee_1604 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1881 edgeNode_1962=true :=
  by decide +kernel

theorem self128_1605 : edgeNode_1963.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1599 self128_1603 apart128_ee_1604

theorem apart128_ee_1606 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1718 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1607 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1799 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1608 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1800 edgeNode_1963=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1606 apart128_ee_1607

theorem self128_1609 : edgeNode_1964.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1595 self128_1605 apart128_ee_1608

theorem apart128_ee_1610 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1311 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1611 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1311 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1612 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1311 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1610 apart128_ee_1611

theorem apart128_ee_1613 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1312 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1614 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1312 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1615 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1312 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1613 apart128_ee_1614

theorem apart128_ee_1616 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1313 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1612 apart128_ee_1615

theorem apart128_ee_1617 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1314 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1618 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1314 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1619 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1314 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1617 apart128_ee_1618

theorem apart128_ee_1620 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1315 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1621 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1315 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1622 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1315 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1620 apart128_ee_1621

theorem apart128_ee_1623 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1316 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1624 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1316 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1625 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1316 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1623 apart128_ee_1624

theorem apart128_ee_1626 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1317 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1622 apart128_ee_1625

theorem apart128_ee_1627 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1318 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1619 apart128_ee_1626

theorem apart128_ee_1628 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1319 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1616 apart128_ee_1627

theorem apart128_ee_1629 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1320 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1630 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1320 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1631 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1320 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1629 apart128_ee_1630

theorem apart128_ee_1632 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1321 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1633 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1321 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1634 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1321 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1632 apart128_ee_1633

theorem apart128_ee_1635 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1322 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1631 apart128_ee_1634

theorem apart128_ee_1636 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1323 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1637 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1323 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1638 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1323 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1636 apart128_ee_1637

theorem apart128_ee_1639 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1324 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1640 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1324 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1641 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1324 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1639 apart128_ee_1640

theorem apart128_ee_1642 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1325 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1643 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1325 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1644 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1325 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1642 apart128_ee_1643

theorem apart128_ee_1645 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1326 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1641 apart128_ee_1644

theorem apart128_ee_1646 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1327 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1638 apart128_ee_1645

theorem apart128_ee_1647 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1328 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1635 apart128_ee_1646

theorem apart128_ee_1648 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1329 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1628 apart128_ee_1647

theorem apart128_ee_1649 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1330 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1650 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1330 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1651 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1330 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1649 apart128_ee_1650

theorem apart128_ee_1652 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1331 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1653 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1331 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1654 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1331 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1652 apart128_ee_1653

theorem apart128_ee_1655 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1332 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1651 apart128_ee_1654

theorem apart128_ee_1656 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1333 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1657 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1333 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1658 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1333 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1656 apart128_ee_1657

theorem apart128_ee_1659 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1334 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1660 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1334 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1661 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1334 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1659 apart128_ee_1660

theorem apart128_ee_1662 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1335 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1663 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1335 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1664 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1335 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1662 apart128_ee_1663

theorem apart128_ee_1665 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1336 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1661 apart128_ee_1664

theorem apart128_ee_1666 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1337 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1658 apart128_ee_1665

theorem apart128_ee_1667 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1338 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1655 apart128_ee_1666

theorem apart128_ee_1668 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1339 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1669 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1339 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1670 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1339 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1668 apart128_ee_1669

theorem apart128_ee_1671 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1340 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1672 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1340 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1673 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1340 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1671 apart128_ee_1672

theorem apart128_ee_1674 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1341 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1670 apart128_ee_1673

theorem apart128_ee_1675 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1342 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1676 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1342 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1677 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1342 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1675 apart128_ee_1676

theorem apart128_ee_1678 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1343 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1679 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1343 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1680 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1343 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1678 apart128_ee_1679

theorem apart128_ee_1681 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1344 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1682 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1344 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1683 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1344 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1681 apart128_ee_1682

theorem apart128_ee_1684 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1345 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1680 apart128_ee_1683

theorem apart128_ee_1685 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1346 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1677 apart128_ee_1684

theorem apart128_ee_1686 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1347 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1674 apart128_ee_1685

theorem apart128_ee_1687 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1348 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1667 apart128_ee_1686

theorem apart128_ee_1688 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1349 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1648 apart128_ee_1687

theorem apart128_ee_1689 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1350 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1690 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1350 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1691 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1350 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1689 apart128_ee_1690

theorem apart128_ee_1692 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1351 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1693 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1351 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1694 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1351 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1692 apart128_ee_1693

theorem apart128_ee_1695 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1352 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1691 apart128_ee_1694

theorem apart128_ee_1696 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1353 edgeNode_1800=true :=
  by decide +kernel

theorem apart128_ee_1697 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1353 edgeNode_1963=true :=
  by decide +kernel

theorem apart128_ee_1698 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1353 edgeNode_1964=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1696 apart128_ee_1697

theorem apart128_ee_1699 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1354 edgeNode_1800=true :=
  by decide +kernel

end PlanarHom.ColoringWireMacroCoordinates
