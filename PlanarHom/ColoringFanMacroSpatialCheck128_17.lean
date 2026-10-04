import PlanarHom.ColoringFanMacroSpatialCheck128_16
noncomputable section
namespace PlanarHom.ColoringFanMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ee_1700 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1506 edgeNode_1547=true :=
  by decide +kernel

theorem self128_1701 : edgeNode_1548.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1698 self128_1699 apart128_ee_1700

theorem self128_1702 : edgeNode_1587.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1703 : edgeNode_1628.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1704 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1587 edgeNode_1628=true :=
  by decide +kernel

theorem self128_1705 : edgeNode_1629.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1702 self128_1703 apart128_ee_1704

theorem apart128_ee_1706 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1548 edgeNode_1629=true :=
  by decide +kernel

theorem self128_1707 : edgeNode_1630.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1701 self128_1705 apart128_ee_1706

theorem apart128_ee_1708 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1385 edgeNode_1630=true :=
  by decide +kernel

theorem apart128_ee_1709 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1466 edgeNode_1630=true :=
  by decide +kernel

theorem apart128_ee_1710 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1467 edgeNode_1630=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1708 apart128_ee_1709

theorem self128_1711 : edgeNode_1631.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1697 self128_1707 apart128_ee_1710

theorem self128_1712 : edgeNode_1670.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1713 : edgeNode_1711.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1714 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1670 edgeNode_1711=true :=
  by decide +kernel

theorem self128_1715 : edgeNode_1712.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1712 self128_1713 apart128_ee_1714

theorem self128_1716 : edgeNode_1751.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1717 : edgeNode_1792.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1718 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1751 edgeNode_1792=true :=
  by decide +kernel

theorem self128_1719 : edgeNode_1793.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1716 self128_1717 apart128_ee_1718

theorem apart128_ee_1720 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1712 edgeNode_1793=true :=
  by decide +kernel

theorem self128_1721 : edgeNode_1794.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1715 self128_1719 apart128_ee_1720

theorem self128_1722 : edgeNode_1833.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1723 : edgeNode_1874.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1724 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1833 edgeNode_1874=true :=
  by decide +kernel

theorem self128_1725 : edgeNode_1875.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1722 self128_1723 apart128_ee_1724

theorem self128_1726 : edgeNode_1914.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem self128_1727 : edgeNode_1955.selfApart (edgePairCheck graph point)=true :=
  by decide +kernel

theorem apart128_ee_1728 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1914 edgeNode_1955=true :=
  by decide +kernel

theorem self128_1729 : edgeNode_1956.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1726 self128_1727 apart128_ee_1728

theorem apart128_ee_1730 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1875 edgeNode_1956=true :=
  by decide +kernel

theorem self128_1731 : edgeNode_1957.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1725 self128_1729 apart128_ee_1730

theorem apart128_ee_1732 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1712 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1733 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1793 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1734 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1794 edgeNode_1957=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1732 apart128_ee_1733

theorem self128_1735 : edgeNode_1958.selfApart (edgePairCheck graph point)=true :=
  IntegerDrawingSpatialCertificate.Tree.selfApart_node self128_1721 self128_1731 apart128_ee_1734

theorem apart128_ee_1736 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1307 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1737 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1307 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1738 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1307 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1736 apart128_ee_1737

theorem apart128_ee_1739 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1308 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1740 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1308 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1741 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1308 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1739 apart128_ee_1740

theorem apart128_ee_1742 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1309 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1738 apart128_ee_1741

theorem apart128_ee_1743 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1310 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1744 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1310 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1745 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1310 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1743 apart128_ee_1744

theorem apart128_ee_1746 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1311 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1747 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1311 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1748 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1311 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1746 apart128_ee_1747

theorem apart128_ee_1749 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1312 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1750 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1312 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1751 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1312 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1749 apart128_ee_1750

theorem apart128_ee_1752 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1313 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1748 apart128_ee_1751

theorem apart128_ee_1753 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1314 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1745 apart128_ee_1752

theorem apart128_ee_1754 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1315 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1742 apart128_ee_1753

theorem apart128_ee_1755 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1316 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1756 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1316 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1757 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1316 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1755 apart128_ee_1756

theorem apart128_ee_1758 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1317 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1759 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1317 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1760 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1317 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1758 apart128_ee_1759

theorem apart128_ee_1761 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1318 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1757 apart128_ee_1760

theorem apart128_ee_1762 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1319 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1763 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1319 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1764 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1319 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1762 apart128_ee_1763

theorem apart128_ee_1765 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1320 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1766 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1320 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1767 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1320 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1765 apart128_ee_1766

theorem apart128_ee_1768 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1321 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1769 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1321 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1770 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1321 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1768 apart128_ee_1769

theorem apart128_ee_1771 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1322 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1767 apart128_ee_1770

theorem apart128_ee_1772 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1323 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1764 apart128_ee_1771

theorem apart128_ee_1773 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1324 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1761 apart128_ee_1772

theorem apart128_ee_1774 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1325 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1754 apart128_ee_1773

theorem apart128_ee_1775 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1326 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1776 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1326 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1777 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1326 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1775 apart128_ee_1776

theorem apart128_ee_1778 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1327 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1779 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1327 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1780 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1327 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1778 apart128_ee_1779

theorem apart128_ee_1781 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1328 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1777 apart128_ee_1780

theorem apart128_ee_1782 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1329 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1783 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1329 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1784 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1329 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1782 apart128_ee_1783

theorem apart128_ee_1785 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1330 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1786 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1330 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1787 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1330 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1785 apart128_ee_1786

theorem apart128_ee_1788 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1331 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1789 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1331 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1790 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1331 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1788 apart128_ee_1789

theorem apart128_ee_1791 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1332 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1787 apart128_ee_1790

theorem apart128_ee_1792 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1333 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1784 apart128_ee_1791

theorem apart128_ee_1793 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1334 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ee_1781 apart128_ee_1792

theorem apart128_ee_1794 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1335 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1795 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1335 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1796 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1335 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1794 apart128_ee_1795

theorem apart128_ee_1797 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1336 edgeNode_1794=true :=
  by decide +kernel

theorem apart128_ee_1798 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1336 edgeNode_1957=true :=
  by decide +kernel

theorem apart128_ee_1799 : IntegerDrawingSpatialCertificate.Tree.apart (edgePairCheck graph point) edgeNode_1336 edgeNode_1958=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_leaf_node apart128_ee_1797 apart128_ee_1798

end PlanarHom.ColoringFanMacroCoordinates
