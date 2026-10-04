import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.WireFramed
private def rootValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 1) else (if i < 3 then 2 else 3)) else (if i < 6 then (if i < 5 then 4 else 5) else (if i < 7 then 6 else 7))) else (if i < 12 then (if i < 10 then (if i < 9 then 16 else 17) else (if i < 11 then 18 else 19)) else (if i < 14 then (if i < 13 then 20 else 21) else (if i < 15 then 22 else 23)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 32 else 33) else (if i < 19 then 34 else 36)) else (if i < 22 then (if i < 21 then 38 else 48) else (if i < 23 then 49 else 50))) else (if i < 28 then (if i < 26 then (if i < 25 then 52 else 54) else (if i < 27 then 55 else 64)) else (if i < 30 then (if i < 29 then 66 else 67) else (if i < 31 then 68 else 69)))))

private def rootValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 70 else 86) else (if i < 35 then 100 else 101)) else (if i < 38 then (if i < 37 then 103 else 104) else (if i < 39 then 105 else 106))) else (if i < 44 then (if i < 42 then (if i < 41 then 107 else 117) else (if i < 43 then 118 else 119)) else (if i < 46 then (if i < 45 then 120 else 121) else (if i < 47 then 122 else 123)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 139 else 152) else (if i < 51 then 153 else 154)) else (if i < 54 then (if i < 53 then 155 else 156) else (if i < 55 then 157 else 158))) else (if i < 60 then (if i < 58 then (if i < 57 then 159 else 168) else (if i < 59 then 169 else 170)) else (if i < 62 then (if i < 61 then 171 else 172) else (if i < 63 then 173 else 174)))))

private def rootValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 175 else 184) else (if i < 67 then 185 else 186)) else (if i < 70 then (if i < 69 then 188 else 190) else (if i < 71 then 200 else 201))) else (if i < 76 then (if i < 74 then (if i < 73 then 202 else 204) else (if i < 75 then 206 else 207)) else (if i < 78 then (if i < 77 then 216 else 218) else (if i < 79 then 219 else 220)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 221 else 222) else (if i < 83 then 238 else 252)) else (if i < 86 then (if i < 85 then 253 else 255) else (if i < 87 then 256 else 257))) else (if i < 92 then (if i < 90 then (if i < 89 then 258 else 259) else (if i < 91 then 269 else 270)) else (if i < 94 then (if i < 93 then 271 else 272) else (if i < 95 then 273 else 274)))))

private def rootValue_b3 (i : ℕ) : ℕ :=
  (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 275 else 291) else (if i < 99 then 304 else 305)) else (if i < 102 then (if i < 101 then 306 else 307) else (if i < 103 then 308 else 309))) else (if i < 108 then (if i < 106 then (if i < 105 then 310 else 311) else (if i < 107 then 320 else 321)) else (if i < 110 then (if i < 109 then 322 else 323) else (if i < 111 then 324 else 325)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 326 else 327) else (if i < 115 then 336 else 337)) else (if i < 118 then (if i < 117 then 338 else 340) else (if i < 119 then 342 else 352))) else (if i < 124 then (if i < 122 then (if i < 121 then 353 else 354) else (if i < 123 then 356 else 358)) else (if i < 126 then (if i < 125 then 359 else 368) else (if i < 127 then 370 else 371)))))

private def rootValue_b4 (i : ℕ) : ℕ :=
  (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 372 else 373) else (if i < 131 then 374 else 390)) else (if i < 134 then (if i < 133 then 404 else 405) else (if i < 135 then 407 else 408))) else (if i < 140 then (if i < 138 then (if i < 137 then 409 else 410) else (if i < 139 then 411 else 421)) else (if i < 142 then (if i < 141 then 422 else 423) else (if i < 143 then 424 else 425)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 427 else 443) else (if i < 147 then 457 else 459)) else (if i < 150 then (if i < 149 then 460 else 461) else (if i < 151 then 471 else 473))) else (if i < 156 then (if i < 154 then (if i < 153 then 474 else 475) else (if i < 155 then 485 else 487)) else (if i < 158 then (if i < 157 then 488 else 489) else (if i < 159 then 498 else 508)))))

private def rootValue_b5 (i : ℕ) : ℕ :=
  (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 510 else 511) else (if i < 163 then 512 else 513)) else (if i < 166 then (if i < 165 then 514 else 524) else (if i < 167 then 525 else 526))) else (if i < 172 then (if i < 170 then (if i < 169 then 527 else 528) else (if i < 171 then 529 else 530)) else (if i < 174 then (if i < 173 then 531 else 540) else (if i < 175 then 541 else 542)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 544 else 546) else (if i < 179 then 556 else 557)) else (if i < 182 then (if i < 181 then 558 else 560) else (if i < 183 then 562 else 563))) else (if i < 188 then (if i < 186 then (if i < 185 then 572 else 574) else (if i < 187 then 575 else 576)) else (if i < 190 then (if i < 189 then 577 else 578) else (if i < 191 then 594 else 608)))))

private def rootValue_b6 (i : ℕ) : ℕ :=
  (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 609 else 611) else (if i < 195 then 612 else 613)) else (if i < 198 then (if i < 197 then 614 else 615) else (if i < 199 then 625 else 626))) else (if i < 204 then (if i < 202 then (if i < 201 then 627 else 628) else (if i < 203 then 629 else 630)) else (if i < 206 then (if i < 205 then 631 else 647) else (if i < 207 then 660 else 661)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 662 else 663) else (if i < 211 then 664 else 665)) else (if i < 214 then (if i < 213 then 666 else 676) else (if i < 215 then 677 else 678))) else (if i < 220 then (if i < 218 then (if i < 217 then 679 else 680) else (if i < 219 then 681 else 682)) else (if i < 222 then (if i < 221 then 683 else 692) else (if i < 223 then 693 else 694)))))

private def rootValue_b7 (i : ℕ) : ℕ :=
  (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 696 else 698) else (if i < 227 then 708 else 709)) else (if i < 230 then (if i < 229 then 710 else 712) else (if i < 231 then 714 else 715))) else (if i < 236 then (if i < 234 then (if i < 233 then 724 else 726) else (if i < 235 then 727 else 728)) else (if i < 238 then (if i < 237 then 729 else 730) else (if i < 239 then 746 else 760)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 761 else 763) else (if i < 243 then 764 else 765)) else (if i < 246 then (if i < 245 then 766 else 767) else (if i < 247 then 777 else 778))) else (if i < 252 then (if i < 250 then (if i < 249 then 779 else 780) else (if i < 251 then 781 else 782)) else (if i < 254 then (if i < 253 then 783 else 799) else (if i < 255 then 812 else 814)))))

private def rootValue_b8 (i : ℕ) : ℕ :=
  (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 815 else 816) else (if i < 259 then 817 else 818)) else (if i < 262 then (if i < 261 then 828 else 829) else (if i < 263 then 830 else 831))) else (if i < 268 then (if i < 266 then (if i < 265 then 832 else 833) else (if i < 267 then 834 else 835)) else (if i < 270 then (if i < 269 then 844 else 845) else (if i < 271 then 846 else 848)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 850 else 860) else (if i < 275 then 861 else 862)) else (if i < 278 then (if i < 277 then 864 else 866) else (if i < 279 then 867 else 876))) else (if i < 284 then (if i < 282 then (if i < 281 then 878 else 879) else (if i < 283 then 880 else 881)) else (if i < 286 then (if i < 285 then 882 else 898) else (if i < 287 then 912 else 913)))))

private def rootValue_b9 (i : ℕ) : ℕ :=
  (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 915 else 916) else (if i < 291 then 917 else 918)) else (if i < 294 then (if i < 293 then 919 else 929) else (if i < 295 then 930 else 931))) else (if i < 300 then (if i < 298 then (if i < 297 then 932 else 933) else (if i < 299 then 935 else 951)) else (if i < 302 then (if i < 301 then 965 else 967) else (if i < 303 then 969 else 979)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 981 else 982) else (if i < 307 then 983 else 993)) else (if i < 310 then (if i < 309 then 995 else 996) else (if i < 311 then 997 else 1006))) else (if i < 316 then (if i < 314 then (if i < 313 then 1016 else 1017) else (if i < 315 then 1018 else 1019)) else (if i < 318 then (if i < 317 then 1020 else 1021) else (if i < 319 then 1022 else 1023)))))

private def rootValue_b10 (i : ℕ) : ℕ :=
  (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 1032 else 1033) else (if i < 323 then 1034 else 1035)) else (if i < 326 then (if i < 325 then 1036 else 1037) else (if i < 327 then 1038 else 1039))) else (if i < 332 then (if i < 330 then (if i < 329 then 1048 else 1049) else (if i < 331 then 1050 else 1052)) else (if i < 334 then (if i < 333 then 1054 else 1064) else (if i < 335 then 1065 else 1066)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 1068 else 1070) else (if i < 339 then 1071 else 1080)) else (if i < 342 then (if i < 341 then 1082 else 1083) else (if i < 343 then 1084 else 1085))) else (if i < 348 then (if i < 346 then (if i < 345 then 1086 else 1102) else (if i < 347 then 1116 else 1117)) else (if i < 350 then (if i < 349 then 1119 else 1120) else (if i < 351 then 1121 else 1122)))))

private def rootValue_b11 (i : ℕ) : ℕ :=
  (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 1123 else 1133) else (if i < 355 then 1134 else 1135)) else (if i < 358 then (if i < 357 then 1136 else 1137) else (if i < 359 then 1138 else 1139))) else (if i < 364 then (if i < 362 then (if i < 361 then 1155 else 1168) else (if i < 363 then 1170 else 1171)) else (if i < 366 then (if i < 365 then 1172 else 1173) else (if i < 367 then 1174 else 1175)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 1184 else 1185) else (if i < 371 then 1186 else 1187)) else (if i < 374 then (if i < 373 then 1188 else 1189) else (if i < 375 then 1190 else 1191))) else (if i < 380 then (if i < 378 then (if i < 377 then 1200 else 1201) else (if i < 379 then 1202 else 1204)) else (if i < 382 then (if i < 381 then 1206 else 1216) else (if i < 383 then 1217 else 1218)))))

private def rootValue_b12 (i : ℕ) : ℕ :=
  (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 1220 else 1222) else (if i < 387 then 1223 else 1232)) else (if i < 390 then (if i < 389 then 1234 else 1235) else (if i < 391 then 1236 else 1237))) else (if i < 396 then (if i < 394 then (if i < 393 then 1238 else 1254) else (if i < 395 then 1268 else 1269)) else (if i < 398 then (if i < 397 then 1271 else 1272) else (if i < 399 then 1273 else 1274)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 1275 else 1285) else (if i < 403 then 1286 else 1287)) else (if i < 406 then (if i < 405 then 1288 else 1289) else (if i < 407 then 1290 else 1291))) else (if i < 412 then (if i < 410 then (if i < 409 then 1307 else 1320) else (if i < 411 then 1321 else 1322)) else (if i < 414 then (if i < 413 then 1323 else 1324) else (if i < 415 then 1325 else 1326)))))

private def rootValue_b13 (i : ℕ) : ℕ :=
  (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 1336 else 1337) else (if i < 419 then 1338 else 1339)) else (if i < 422 then (if i < 421 then 1340 else 1341) else (if i < 423 then 1342 else 1343))) else (if i < 428 then (if i < 426 then (if i < 425 then 1352 else 1353) else (if i < 427 then 1354 else 1356)) else (if i < 430 then (if i < 429 then 1358 else 1368) else (if i < 431 then 1369 else 1370)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 1372 else 1374) else (if i < 435 then 1375 else 1384)) else (if i < 438 then (if i < 437 then 1386 else 1387) else (if i < 439 then 1388 else 1389))) else (if i < 444 then (if i < 442 then (if i < 441 then 1390 else 1406) else (if i < 443 then 1420 else 1421)) else (if i < 446 then (if i < 445 then 1423 else 1424) else (if i < 447 then 1425 else 1426)))))

private def rootValue_b14 (i : ℕ) : ℕ :=
  (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 1427 else 1437) else (if i < 451 then 1438 else 1439)) else (if i < 454 then (if i < 453 then 1440 else 1441) else (if i < 455 then 1443 else 1459))) else (if i < 460 then (if i < 458 then (if i < 457 then 1473 else 1475) else (if i < 459 then 1476 else 1477)) else (if i < 462 then (if i < 461 then 1487 else 1489) else (if i < 463 then 1490 else 1491)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 1501 else 1503) else (if i < 467 then 1504 else 1505)) else (if i < 470 then (if i < 469 then 1514 else 1524) else (if i < 471 then 1525 else 1526))) else (if i < 476 then (if i < 474 then (if i < 473 then 1527 else 1528) else (if i < 475 then 1529 else 1530)) else (if i < 478 then (if i < 477 then 1540 else 1541) else (if i < 479 then 1542 else 1543)))))

private def rootValue_b15 (i : ℕ) : ℕ :=
  (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 1544 else 1545) else (if i < 483 then 1546 else 1547)) else (if i < 486 then (if i < 485 then 1556 else 1557) else (if i < 487 then 1558 else 1560))) else (if i < 492 then (if i < 490 then (if i < 489 then 1562 else 1572) else (if i < 491 then 1573 else 1574)) else (if i < 494 then (if i < 493 then 1576 else 1578) else (if i < 495 then 1579 else 1588)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 1590 else 1591) else (if i < 499 then 1592 else 1593)) else (if i < 502 then (if i < 501 then 1594 else 1610) else (if i < 503 then 1624 else 1625))) else (if i < 508 then (if i < 506 then (if i < 505 then 1627 else 1628) else (if i < 507 then 1629 else 1630)) else (if i < 510 then (if i < 509 then 1631 else 1641) else (if i < 511 then 1642 else 1643)))))

private def rootValue_b16 (i : ℕ) : ℕ :=
  (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 1644 else 1645) else (if i < 515 then 1646 else 1647)) else (if i < 518 then (if i < 517 then 1663 else 1676) else (if i < 519 then 1678 else 1679))) else (if i < 524 then (if i < 522 then (if i < 521 then 1680 else 1681) else (if i < 523 then 1682 else 1692)) else (if i < 526 then (if i < 525 then 1693 else 1694) else (if i < 527 then 1695 else 1696)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 1697 else 1698) else (if i < 531 then 1699 else 1708)) else (if i < 534 then (if i < 533 then 1709 else 1710) else (if i < 535 then 1712 else 1714))) else (if i < 540 then (if i < 538 then (if i < 537 then 1724 else 1725) else (if i < 539 then 1726 else 1728)) else (if i < 542 then (if i < 541 then 1730 else 1731) else (if i < 543 then 1740 else 1742)))))

private def rootValue_b17 (i : ℕ) : ℕ :=
  (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then 1743 else 1744) else (if i < 547 then 1745 else 1746)) else (if i < 550 then (if i < 549 then 1762 else 1776) else (if i < 551 then 1777 else 1779))) else (if i < 556 then (if i < 554 then (if i < 553 then 1780 else 1781) else (if i < 555 then 1782 else 1783)) else (if i < 558 then (if i < 557 then 1793 else 1794) else (if i < 559 then 1795 else 1796)))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then 1797 else 1798) else (if i < 563 then 1799 else 1815)) else (if i < 566 then (if i < 565 then 1828 else 1830) else (if i < 567 then 1831 else 1832))) else (if i < 572 then (if i < 570 then (if i < 569 then 1833 else 1834) else (if i < 571 then 1844 else 1845)) else (if i < 574 then (if i < 573 then 1846 else 1847) else (if i < 575 then 1848 else 1849)))))

private def rootValue_b18 (i : ℕ) : ℕ :=
  (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then 1850 else 1851) else (if i < 579 then 1860 else 1861)) else (if i < 582 then (if i < 581 then 1862 else 1864) else (if i < 583 then 1866 else 1876))) else (if i < 588 then (if i < 586 then (if i < 585 then 1877 else 1878) else (if i < 587 then 1880 else 1882)) else (if i < 590 then (if i < 589 then 1883 else 1892) else (if i < 591 then 1894 else 1895)))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then 1896 else 1897) else (if i < 595 then 1898 else 1914)) else (if i < 598 then (if i < 597 then 1928 else 1929) else (if i < 599 then 1931 else 1932))) else (if i < 604 then (if i < 602 then (if i < 601 then 1933 else 1934) else (if i < 603 then 1935 else 1945)) else (if i < 606 then (if i < 605 then 1946 else 1947) else (if i < 607 then 1948 else 1949)))))

private def rootValue_b19 (i : ℕ) : ℕ :=
  (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then 1951 else 1967) else (if i < 611 then 1981 else 1983)) else (if i < 614 then (if i < 613 then 1985 else 1995) else (if i < 615 then 1997 else 1998))) else (if i < 620 then (if i < 618 then (if i < 617 then 1999 else 2009) else (if i < 619 then 2011 else 2013)) else (if i < 622 then (if i < 621 then 2022 else 2032) else (if i < 623 then 2034 else 2035)))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then 2036 else 2037) else (if i < 627 then 2038 else 2048)) else (if i < 630 then (if i < 629 then 2049 else 2050) else (if i < 631 then 2051 else 2052))) else (if i < 636 then (if i < 634 then (if i < 633 then 2053 else 2054) else (if i < 635 then 2055 else 2064)) else (if i < 638 then (if i < 637 then 2065 else 2066) else (if i < 639 then 2068 else 2070)))))

private def rootValue_b20 (i : ℕ) : ℕ :=
  (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then 2080 else 2081) else (if i < 643 then 2082 else 2084)) else (if i < 646 then (if i < 645 then 2086 else 2087) else (if i < 647 then 2096 else 2098))) else (if i < 652 then (if i < 650 then (if i < 649 then 2099 else 2100) else (if i < 651 then 2101 else 2102)) else (if i < 654 then (if i < 653 then 2118 else 2132) else (if i < 655 then 2133 else 2135)))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then 2136 else 2137) else (if i < 659 then 2138 else 2139)) else (if i < 662 then (if i < 661 then 2149 else 2150) else (if i < 663 then 2151 else 2152))) else (if i < 668 then (if i < 666 then (if i < 665 then 2153 else 2154) else (if i < 667 then 2155 else 2171)) else (if i < 670 then (if i < 669 then 2184 else 2186) else (if i < 671 then 2187 else 2188)))))

private def rootValue_b21 (i : ℕ) : ℕ :=
  (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then 2189 else 2190) else (if i < 675 then 2200 else 2201)) else (if i < 678 then (if i < 677 then 2202 else 2203) else (if i < 679 then 2204 else 2205))) else (if i < 684 then (if i < 682 then (if i < 681 then 2206 else 2207) else (if i < 683 then 2216 else 2217)) else (if i < 686 then (if i < 685 then 2218 else 2220) else (if i < 687 then 2222 else 2232)))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then 2233 else 2234) else (if i < 691 then 2236 else 2238)) else (if i < 694 then (if i < 693 then 2239 else 2248) else (if i < 695 then 2250 else 2251))) else (if i < 700 then (if i < 698 then (if i < 697 then 2252 else 2253) else (if i < 699 then 2254 else 2270)) else (if i < 702 then (if i < 701 then 2284 else 2285) else (if i < 703 then 2287 else 2288)))))

private def rootValue_b22 (i : ℕ) : ℕ :=
  (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then 2289 else 2290) else (if i < 707 then 2291 else 2301)) else (if i < 710 then (if i < 709 then 2302 else 2303) else (if i < 711 then 2304 else 2305))) else (if i < 716 then (if i < 714 then (if i < 713 then 2306 else 2307) else (if i < 715 then 2323 else 2336)) else (if i < 718 then (if i < 717 then 2338 else 2339) else (if i < 719 then 2340 else 2341)))) else (if i < 728 then (if i < 724 then (if i < 722 then (if i < 721 then 2342 else 2352) else (if i < 723 then 2353 else 2354)) else (if i < 726 then (if i < 725 then 2355 else 2356) else (if i < 727 then 2357 else 2358))) else (if i < 732 then (if i < 730 then (if i < 729 then 2359 else 2368) else (if i < 731 then 2369 else 2370)) else (if i < 734 then (if i < 733 then 2372 else 2374) else (if i < 735 then 2384 else 2385)))))

private def rootValue_b23 (i : ℕ) : ℕ :=
  (if i < 752 then (if i < 744 then (if i < 740 then (if i < 738 then (if i < 737 then 2386 else 2388) else (if i < 739 then 2390 else 2391)) else (if i < 742 then (if i < 741 then 2400 else 2402) else (if i < 743 then 2403 else 2404))) else (if i < 748 then (if i < 746 then (if i < 745 then 2405 else 2406) else (if i < 747 then 2422 else 2436)) else (if i < 750 then (if i < 749 then 2437 else 2439) else (if i < 751 then 2440 else 2441)))) else (if i < 760 then (if i < 756 then (if i < 754 then (if i < 753 then 2442 else 2443) else (if i < 755 then 2453 else 2454)) else (if i < 758 then (if i < 757 then 2455 else 2456) else (if i < 759 then 2457 else 2459))) else (if i < 764 then (if i < 762 then (if i < 761 then 2475 else 2489) else (if i < 763 then 2491 else 2493)) else (if i < 766 then (if i < 765 then 2503 else 2505) else (if i < 767 then 2506 else 2507)))))

private def rootValue_b24 (i : ℕ) : ℕ :=
  (if i < 779 then (if i < 773 then (if i < 770 then (if i < 769 then 2517 else 2519) else (if i < 771 then 2521 else (if i < 772 then 2530 else 2540))) else (if i < 776 then (if i < 774 then 2541 else (if i < 775 then 2543 else 2545)) else (if i < 777 then 2554 else (if i < 778 then 2556 else 2563)))) else (if i < 785 then (if i < 782 then (if i < 780 then 2567 else (if i < 781 then 2569 else 2574)) else (if i < 783 then 2579 else (if i < 784 then 2581 else 2591))) else (if i < 788 then (if i < 786 then 2593 else (if i < 787 then 2603 else 2605)) else (if i < 789 then 2615 else (if i < 790 then 2617 else 2645)))))

private def rootValue_n0_0 (i : ℕ) : ℕ := if i < 32 then rootValue_b0 i else rootValue_b1 i

private def rootValue_n0_1 (i : ℕ) : ℕ := if i < 96 then rootValue_b2 i else rootValue_b3 i

private def rootValue_n0_2 (i : ℕ) : ℕ := if i < 160 then rootValue_b4 i else rootValue_b5 i

private def rootValue_n0_3 (i : ℕ) : ℕ := if i < 224 then rootValue_b6 i else rootValue_b7 i

private def rootValue_n0_4 (i : ℕ) : ℕ := if i < 288 then rootValue_b8 i else rootValue_b9 i

private def rootValue_n0_5 (i : ℕ) : ℕ := if i < 352 then rootValue_b10 i else rootValue_b11 i

private def rootValue_n0_6 (i : ℕ) : ℕ := if i < 416 then rootValue_b12 i else rootValue_b13 i

private def rootValue_n0_7 (i : ℕ) : ℕ := if i < 480 then rootValue_b14 i else rootValue_b15 i

private def rootValue_n0_8 (i : ℕ) : ℕ := if i < 544 then rootValue_b16 i else rootValue_b17 i

private def rootValue_n0_9 (i : ℕ) : ℕ := if i < 608 then rootValue_b18 i else rootValue_b19 i

private def rootValue_n0_10 (i : ℕ) : ℕ := if i < 672 then rootValue_b20 i else rootValue_b21 i

private def rootValue_n0_11 (i : ℕ) : ℕ := if i < 736 then rootValue_b22 i else rootValue_b23 i

private def rootValue_n1_0 (i : ℕ) : ℕ := if i < 64 then rootValue_n0_0 i else rootValue_n0_1 i

private def rootValue_n1_1 (i : ℕ) : ℕ := if i < 192 then rootValue_n0_2 i else rootValue_n0_3 i

private def rootValue_n1_2 (i : ℕ) : ℕ := if i < 320 then rootValue_n0_4 i else rootValue_n0_5 i

private def rootValue_n1_3 (i : ℕ) : ℕ := if i < 448 then rootValue_n0_6 i else rootValue_n0_7 i

private def rootValue_n1_4 (i : ℕ) : ℕ := if i < 576 then rootValue_n0_8 i else rootValue_n0_9 i

private def rootValue_n1_5 (i : ℕ) : ℕ := if i < 704 then rootValue_n0_10 i else rootValue_n0_11 i

private def rootValue_n2_0 (i : ℕ) : ℕ := if i < 128 then rootValue_n1_0 i else rootValue_n1_1 i

private def rootValue_n2_1 (i : ℕ) : ℕ := if i < 384 then rootValue_n1_2 i else rootValue_n1_3 i

private def rootValue_n2_2 (i : ℕ) : ℕ := if i < 640 then rootValue_n1_4 i else rootValue_n1_5 i

private def rootValue_n3_0 (i : ℕ) : ℕ := if i < 256 then rootValue_n2_0 i else rootValue_n2_1 i

private def rootValue_n3_1 (i : ℕ) : ℕ := if i < 768 then rootValue_n2_2 i else rootValue_b24 i

private def rootValue_n4_0 (i : ℕ) : ℕ := if i < 512 then rootValue_n3_0 i else rootValue_n3_1 i

def rootValue (i : ℕ) : ℕ := rootValue_n4_0 i

end PlanarHom.ColoringMacroFaces.WireFramed
