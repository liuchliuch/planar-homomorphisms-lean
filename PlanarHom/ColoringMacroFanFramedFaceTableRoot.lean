import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.FanFramed
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
  (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 509 else 510) else (if i < 163 then 511 else 512)) else (if i < 166 then (if i < 165 then 513 else 514) else (if i < 167 then 524 else 525))) else (if i < 172 then (if i < 170 then (if i < 169 then 526 else 527) else (if i < 171 then 528 else 529)) else (if i < 174 then (if i < 173 then 530 else 531) else (if i < 175 then 540 else 541)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 542 else 544) else (if i < 179 then 546 else 556)) else (if i < 182 then (if i < 181 then 557 else 558) else (if i < 183 then 560 else 562))) else (if i < 188 then (if i < 186 then (if i < 185 then 563 else 572) else (if i < 187 then 574 else 575)) else (if i < 190 then (if i < 189 then 576 else 577) else (if i < 191 then 578 else 594)))))

private def rootValue_b6 (i : ℕ) : ℕ :=
  (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 608 else 609) else (if i < 195 then 611 else 612)) else (if i < 198 then (if i < 197 then 613 else 614) else (if i < 199 then 615 else 625))) else (if i < 204 then (if i < 202 then (if i < 201 then 626 else 627) else (if i < 203 then 628 else 629)) else (if i < 206 then (if i < 205 then 630 else 631) else (if i < 207 then 647 else 660)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 662 else 663) else (if i < 211 then 664 else 665)) else (if i < 214 then (if i < 213 then 666 else 676) else (if i < 215 then 677 else 678))) else (if i < 220 then (if i < 218 then (if i < 217 then 679 else 680) else (if i < 219 then 681 else 682)) else (if i < 222 then (if i < 221 then 683 else 692) else (if i < 223 then 693 else 694)))))

private def rootValue_b7 (i : ℕ) : ℕ :=
  (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 696 else 698) else (if i < 227 then 708 else 709)) else (if i < 230 then (if i < 229 then 710 else 712) else (if i < 231 then 714 else 715))) else (if i < 236 then (if i < 234 then (if i < 233 then 724 else 726) else (if i < 235 then 727 else 728)) else (if i < 238 then (if i < 237 then 729 else 730) else (if i < 239 then 746 else 760)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 761 else 763) else (if i < 243 then 764 else 765)) else (if i < 246 then (if i < 245 then 766 else 767) else (if i < 247 then 777 else 778))) else (if i < 252 then (if i < 250 then (if i < 249 then 779 else 780) else (if i < 251 then 781 else 782)) else (if i < 254 then (if i < 253 then 783 else 799) else (if i < 255 then 812 else 814)))))

private def rootValue_b8 (i : ℕ) : ℕ :=
  (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 815 else 816) else (if i < 259 then 817 else 818)) else (if i < 262 then (if i < 261 then 828 else 829) else (if i < 263 then 830 else 831))) else (if i < 268 then (if i < 266 then (if i < 265 then 832 else 833) else (if i < 267 then 834 else 835)) else (if i < 270 then (if i < 269 then 844 else 845) else (if i < 271 then 846 else 848)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 850 else 860) else (if i < 275 then 861 else 862)) else (if i < 278 then (if i < 277 then 864 else 866) else (if i < 279 then 867 else 876))) else (if i < 284 then (if i < 282 then (if i < 281 then 878 else 879) else (if i < 283 then 880 else 881)) else (if i < 286 then (if i < 285 then 882 else 898) else (if i < 287 then 912 else 913)))))

private def rootValue_b9 (i : ℕ) : ℕ :=
  (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 915 else 916) else (if i < 291 then 917 else 918)) else (if i < 294 then (if i < 293 then 919 else 929) else (if i < 295 then 930 else 931))) else (if i < 300 then (if i < 298 then (if i < 297 then 932 else 933) else (if i < 299 then 935 else 951)) else (if i < 302 then (if i < 301 then 965 else 967) else (if i < 303 then 968 else 969)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 979 else 981) else (if i < 307 then 982 else 983)) else (if i < 310 then (if i < 309 then 993 else 995) else (if i < 311 then 997 else 1006))) else (if i < 316 then (if i < 314 then (if i < 313 then 1016 else 1017) else (if i < 315 then 1018 else 1019)) else (if i < 318 then (if i < 317 then 1020 else 1021) else (if i < 319 then 1022 else 1023)))))

private def rootValue_b10 (i : ℕ) : ℕ :=
  (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 1032 else 1033) else (if i < 323 then 1034 else 1035)) else (if i < 326 then (if i < 325 then 1036 else 1037) else (if i < 327 then 1038 else 1039))) else (if i < 332 then (if i < 330 then (if i < 329 then 1048 else 1049) else (if i < 331 then 1050 else 1052)) else (if i < 334 then (if i < 333 then 1054 else 1064) else (if i < 335 then 1065 else 1066)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 1068 else 1070) else (if i < 339 then 1071 else 1080)) else (if i < 342 then (if i < 341 then 1082 else 1083) else (if i < 343 then 1084 else 1085))) else (if i < 348 then (if i < 346 then (if i < 345 then 1086 else 1102) else (if i < 347 then 1116 else 1117)) else (if i < 350 then (if i < 349 then 1119 else 1120) else (if i < 351 then 1121 else 1122)))))

private def rootValue_b11 (i : ℕ) : ℕ :=
  (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 1123 else 1133) else (if i < 355 then 1134 else 1135)) else (if i < 358 then (if i < 357 then 1136 else 1137) else (if i < 359 then 1138 else 1139))) else (if i < 364 then (if i < 362 then (if i < 361 then 1155 else 1168) else (if i < 363 then 1170 else 1171)) else (if i < 366 then (if i < 365 then 1172 else 1173) else (if i < 367 then 1174 else 1175)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 1184 else 1185) else (if i < 371 then 1186 else 1187)) else (if i < 374 then (if i < 373 then 1188 else 1189) else (if i < 375 then 1190 else 1191))) else (if i < 380 then (if i < 378 then (if i < 377 then 1200 else 1201) else (if i < 379 then 1202 else 1204)) else (if i < 382 then (if i < 381 then 1206 else 1216) else (if i < 383 then 1217 else 1218)))))

private def rootValue_b12 (i : ℕ) : ℕ :=
  (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 1220 else 1222) else (if i < 387 then 1223 else 1232)) else (if i < 390 then (if i < 389 then 1234 else 1235) else (if i < 391 then 1236 else 1237))) else (if i < 396 then (if i < 394 then (if i < 393 then 1238 else 1254) else (if i < 395 then 1268 else 1269)) else (if i < 398 then (if i < 397 then 1271 else 1272) else (if i < 399 then 1273 else 1274)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 1275 else 1285) else (if i < 403 then 1286 else 1287)) else (if i < 406 then (if i < 405 then 1288 else 1289) else (if i < 407 then 1290 else 1291))) else (if i < 412 then (if i < 410 then (if i < 409 then 1307 else 1320) else (if i < 411 then 1321 else 1322)) else (if i < 414 then (if i < 413 then 1323 else 1324) else (if i < 415 then 1325 else 1326)))))

private def rootValue_b13 (i : ℕ) : ℕ :=
  (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 1336 else 1337) else (if i < 419 then 1338 else 1339)) else (if i < 422 then (if i < 421 then 1340 else 1341) else (if i < 423 then 1342 else 1343))) else (if i < 428 then (if i < 426 then (if i < 425 then 1352 else 1353) else (if i < 427 then 1354 else 1356)) else (if i < 430 then (if i < 429 then 1358 else 1368) else (if i < 431 then 1369 else 1370)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 1372 else 1374) else (if i < 435 then 1375 else 1384)) else (if i < 438 then (if i < 437 then 1386 else 1387) else (if i < 439 then 1388 else 1389))) else (if i < 444 then (if i < 442 then (if i < 441 then 1390 else 1406) else (if i < 443 then 1420 else 1421)) else (if i < 446 then (if i < 445 then 1423 else 1424) else (if i < 447 then 1425 else 1426)))))

private def rootValue_b14 (i : ℕ) : ℕ :=
  (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 1427 else 1437) else (if i < 451 then 1438 else 1439)) else (if i < 454 then (if i < 453 then 1440 else 1441) else (if i < 455 then 1443 else 1459))) else (if i < 460 then (if i < 458 then (if i < 457 then 1473 else 1475) else (if i < 459 then 1476 else 1477)) else (if i < 462 then (if i < 461 then 1487 else 1489) else (if i < 463 then 1490 else 1491)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 1501 else 1503) else (if i < 467 then 1504 else 1505)) else (if i < 470 then (if i < 469 then 1514 else 1524) else (if i < 471 then 1526 else 1527))) else (if i < 476 then (if i < 474 then (if i < 473 then 1528 else 1529) else (if i < 475 then 1530 else 1531)) else (if i < 478 then (if i < 477 then 1540 else 1541) else (if i < 479 then 1542 else 1543)))))

private def rootValue_b15 (i : ℕ) : ℕ :=
  (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 1544 else 1545) else (if i < 483 then 1546 else 1547)) else (if i < 486 then (if i < 485 then 1556 else 1557) else (if i < 487 then 1558 else 1560))) else (if i < 492 then (if i < 490 then (if i < 489 then 1562 else 1572) else (if i < 491 then 1573 else 1574)) else (if i < 494 then (if i < 493 then 1576 else 1578) else (if i < 495 then 1579 else 1588)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 1590 else 1591) else (if i < 499 then 1592 else 1593)) else (if i < 502 then (if i < 501 then 1594 else 1610) else (if i < 503 then 1624 else 1625))) else (if i < 508 then (if i < 506 then (if i < 505 then 1627 else 1628) else (if i < 507 then 1629 else 1630)) else (if i < 510 then (if i < 509 then 1631 else 1641) else (if i < 511 then 1642 else 1643)))))

private def rootValue_b16 (i : ℕ) : ℕ :=
  (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 1644 else 1645) else (if i < 515 then 1646 else 1647)) else (if i < 518 then (if i < 517 then 1663 else 1676) else (if i < 519 then 1678 else 1679))) else (if i < 524 then (if i < 522 then (if i < 521 then 1680 else 1681) else (if i < 523 then 1682 else 1692)) else (if i < 526 then (if i < 525 then 1693 else 1694) else (if i < 527 then 1695 else 1696)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 1697 else 1698) else (if i < 531 then 1699 else 1708)) else (if i < 534 then (if i < 533 then 1709 else 1710) else (if i < 535 then 1712 else 1714))) else (if i < 540 then (if i < 538 then (if i < 537 then 1724 else 1725) else (if i < 539 then 1726 else 1728)) else (if i < 542 then (if i < 541 then 1730 else 1731) else (if i < 543 then 1740 else 1742)))))

private def rootValue_b17 (i : ℕ) : ℕ :=
  (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then 1743 else 1744) else (if i < 547 then 1745 else 1746)) else (if i < 550 then (if i < 549 then 1762 else 1776) else (if i < 551 then 1777 else 1779))) else (if i < 556 then (if i < 554 then (if i < 553 then 1780 else 1781) else (if i < 555 then 1782 else 1783)) else (if i < 558 then (if i < 557 then 1793 else 1794) else (if i < 559 then 1795 else 1796)))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then 1797 else 1798) else (if i < 563 then 1799 else 1815)) else (if i < 566 then (if i < 565 then 1828 else 1830) else (if i < 567 then 1831 else 1832))) else (if i < 572 then (if i < 570 then (if i < 569 then 1833 else 1834) else (if i < 571 then 1844 else 1845)) else (if i < 574 then (if i < 573 then 1846 else 1847) else (if i < 575 then 1848 else 1849)))))

private def rootValue_b18 (i : ℕ) : ℕ :=
  (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then 1850 else 1851) else (if i < 579 then 1860 else 1861)) else (if i < 582 then (if i < 581 then 1862 else 1864) else (if i < 583 then 1866 else 1876))) else (if i < 588 then (if i < 586 then (if i < 585 then 1877 else 1878) else (if i < 587 then 1880 else 1882)) else (if i < 590 then (if i < 589 then 1883 else 1892) else (if i < 591 then 1894 else 1895)))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then 1896 else 1897) else (if i < 595 then 1898 else 1914)) else (if i < 598 then (if i < 597 then 1928 else 1929) else (if i < 599 then 1931 else 1932))) else (if i < 604 then (if i < 602 then (if i < 601 then 1933 else 1934) else (if i < 603 then 1935 else 1945)) else (if i < 606 then (if i < 605 then 1946 else 1947) else (if i < 607 then 1948 else 1949)))))

private def rootValue_b19 (i : ℕ) : ℕ :=
  (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then 1951 else 1967) else (if i < 611 then 1981 else 1983)) else (if i < 614 then (if i < 613 then 1984 else 1985) else (if i < 615 then 1995 else 1997))) else (if i < 620 then (if i < 618 then (if i < 617 then 1999 else 2009) else (if i < 619 then 2011 else 2013)) else (if i < 622 then (if i < 621 then 2022 else 2032) else (if i < 623 then 2034 else 2035)))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then 2036 else 2037) else (if i < 627 then 2038 else 2048)) else (if i < 630 then (if i < 629 then 2049 else 2050) else (if i < 631 then 2051 else 2052))) else (if i < 636 then (if i < 634 then (if i < 633 then 2053 else 2054) else (if i < 635 then 2055 else 2064)) else (if i < 638 then (if i < 637 then 2065 else 2066) else (if i < 639 then 2068 else 2070)))))

private def rootValue_b20 (i : ℕ) : ℕ :=
  (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then 2080 else 2081) else (if i < 643 then 2082 else 2084)) else (if i < 646 then (if i < 645 then 2086 else 2087) else (if i < 647 then 2096 else 2098))) else (if i < 652 then (if i < 650 then (if i < 649 then 2099 else 2100) else (if i < 651 then 2101 else 2102)) else (if i < 654 then (if i < 653 then 2118 else 2132) else (if i < 655 then 2133 else 2135)))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then 2136 else 2137) else (if i < 659 then 2138 else 2139)) else (if i < 662 then (if i < 661 then 2149 else 2150) else (if i < 663 then 2151 else 2152))) else (if i < 668 then (if i < 666 then (if i < 665 then 2153 else 2154) else (if i < 667 then 2155 else 2171)) else (if i < 670 then (if i < 669 then 2184 else 2186) else (if i < 671 then 2187 else 2188)))))

private def rootValue_b21 (i : ℕ) : ℕ :=
  (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then 2189 else 2190) else (if i < 675 then 2200 else 2201)) else (if i < 678 then (if i < 677 then 2202 else 2203) else (if i < 679 then 2204 else 2205))) else (if i < 684 then (if i < 682 then (if i < 681 then 2206 else 2207) else (if i < 683 then 2216 else 2217)) else (if i < 686 then (if i < 685 then 2218 else 2220) else (if i < 687 then 2222 else 2232)))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then 2233 else 2234) else (if i < 691 then 2236 else 2238)) else (if i < 694 then (if i < 693 then 2239 else 2248) else (if i < 695 then 2250 else 2251))) else (if i < 700 then (if i < 698 then (if i < 697 then 2252 else 2253) else (if i < 699 then 2254 else 2270)) else (if i < 702 then (if i < 701 then 2284 else 2285) else (if i < 703 then 2287 else 2288)))))

private def rootValue_b22 (i : ℕ) : ℕ :=
  (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then 2289 else 2290) else (if i < 707 then 2291 else 2301)) else (if i < 710 then (if i < 709 then 2302 else 2303) else (if i < 711 then 2304 else 2305))) else (if i < 716 then (if i < 714 then (if i < 713 then 2306 else 2307) else (if i < 715 then 2323 else 2336)) else (if i < 718 then (if i < 717 then 2338 else 2339) else (if i < 719 then 2340 else 2341)))) else (if i < 728 then (if i < 724 then (if i < 722 then (if i < 721 then 2342 else 2352) else (if i < 723 then 2353 else 2354)) else (if i < 726 then (if i < 725 then 2355 else 2356) else (if i < 727 then 2357 else 2358))) else (if i < 732 then (if i < 730 then (if i < 729 then 2359 else 2368) else (if i < 731 then 2369 else 2370)) else (if i < 734 then (if i < 733 then 2372 else 2374) else (if i < 735 then 2384 else 2385)))))

private def rootValue_b23 (i : ℕ) : ℕ :=
  (if i < 752 then (if i < 744 then (if i < 740 then (if i < 738 then (if i < 737 then 2386 else 2388) else (if i < 739 then 2390 else 2391)) else (if i < 742 then (if i < 741 then 2400 else 2402) else (if i < 743 then 2403 else 2404))) else (if i < 748 then (if i < 746 then (if i < 745 then 2405 else 2406) else (if i < 747 then 2422 else 2436)) else (if i < 750 then (if i < 749 then 2437 else 2439) else (if i < 751 then 2440 else 2441)))) else (if i < 760 then (if i < 756 then (if i < 754 then (if i < 753 then 2442 else 2443) else (if i < 755 then 2453 else 2454)) else (if i < 758 then (if i < 757 then 2455 else 2456) else (if i < 759 then 2457 else 2459))) else (if i < 764 then (if i < 762 then (if i < 761 then 2475 else 2489) else (if i < 763 then 2491 else 2493)) else (if i < 766 then (if i < 765 then 2503 else 2505) else (if i < 767 then 2506 else 2507)))))

private def rootValue_b24 (i : ℕ) : ℕ :=
  (if i < 784 then (if i < 776 then (if i < 772 then (if i < 770 then (if i < 769 then 2517 else 2519) else (if i < 771 then 2521 else 2530)) else (if i < 774 then (if i < 773 then 2540 else 2541) else (if i < 775 then 2542 else 2543))) else (if i < 780 then (if i < 778 then (if i < 777 then 2544 else 2545) else (if i < 779 then 2546 else 2556)) else (if i < 782 then (if i < 781 then 2557 else 2558) else (if i < 783 then 2559 else 2560)))) else (if i < 792 then (if i < 788 then (if i < 786 then (if i < 785 then 2561 else 2562) else (if i < 787 then 2563 else 2572)) else (if i < 790 then (if i < 789 then 2573 else 2574) else (if i < 791 then 2576 else 2578))) else (if i < 796 then (if i < 794 then (if i < 793 then 2588 else 2589) else (if i < 795 then 2590 else 2592)) else (if i < 798 then (if i < 797 then 2594 else 2595) else (if i < 799 then 2604 else 2606)))))

private def rootValue_b25 (i : ℕ) : ℕ :=
  (if i < 816 then (if i < 808 then (if i < 804 then (if i < 802 then (if i < 801 then 2607 else 2608) else (if i < 803 then 2609 else 2610)) else (if i < 806 then (if i < 805 then 2626 else 2640) else (if i < 807 then 2641 else 2643))) else (if i < 812 then (if i < 810 then (if i < 809 then 2644 else 2645) else (if i < 811 then 2646 else 2647)) else (if i < 814 then (if i < 813 then 2657 else 2658) else (if i < 815 then 2659 else 2660)))) else (if i < 824 then (if i < 820 then (if i < 818 then (if i < 817 then 2661 else 2662) else (if i < 819 then 2663 else 2679)) else (if i < 822 then (if i < 821 then 2692 else 2693) else (if i < 823 then 2694 else 2695))) else (if i < 828 then (if i < 826 then (if i < 825 then 2696 else 2697) else (if i < 827 then 2698 else 2699)) else (if i < 830 then (if i < 829 then 2708 else 2709) else (if i < 831 then 2710 else 2711)))))

private def rootValue_b26 (i : ℕ) : ℕ :=
  (if i < 848 then (if i < 840 then (if i < 836 then (if i < 834 then (if i < 833 then 2712 else 2713) else (if i < 835 then 2714 else 2715)) else (if i < 838 then (if i < 837 then 2724 else 2725) else (if i < 839 then 2726 else 2728))) else (if i < 844 then (if i < 842 then (if i < 841 then 2730 else 2740) else (if i < 843 then 2741 else 2742)) else (if i < 846 then (if i < 845 then 2744 else 2746) else (if i < 847 then 2747 else 2756)))) else (if i < 856 then (if i < 852 then (if i < 850 then (if i < 849 then 2758 else 2759) else (if i < 851 then 2760 else 2761)) else (if i < 854 then (if i < 853 then 2762 else 2778) else (if i < 855 then 2792 else 2793))) else (if i < 860 then (if i < 858 then (if i < 857 then 2795 else 2796) else (if i < 859 then 2797 else 2798)) else (if i < 862 then (if i < 861 then 2799 else 2809) else (if i < 863 then 2810 else 2811)))))

private def rootValue_b27 (i : ℕ) : ℕ :=
  (if i < 880 then (if i < 872 then (if i < 868 then (if i < 866 then (if i < 865 then 2812 else 2813) else (if i < 867 then 2814 else 2815)) else (if i < 870 then (if i < 869 then 2831 else 2844) else (if i < 871 then 2846 else 2847))) else (if i < 876 then (if i < 874 then (if i < 873 then 2848 else 2849) else (if i < 875 then 2850 else 2851)) else (if i < 878 then (if i < 877 then 2860 else 2861) else (if i < 879 then 2862 else 2863)))) else (if i < 888 then (if i < 884 then (if i < 882 then (if i < 881 then 2864 else 2865) else (if i < 883 then 2866 else 2867)) else (if i < 886 then (if i < 885 then 2876 else 2877) else (if i < 887 then 2878 else 2880))) else (if i < 892 then (if i < 890 then (if i < 889 then 2882 else 2892) else (if i < 891 then 2893 else 2894)) else (if i < 894 then (if i < 893 then 2896 else 2898) else (if i < 895 then 2899 else 2908)))))

private def rootValue_b28 (i : ℕ) : ℕ :=
  (if i < 912 then (if i < 904 then (if i < 900 then (if i < 898 then (if i < 897 then 2910 else 2911) else (if i < 899 then 2912 else 2913)) else (if i < 902 then (if i < 901 then 2914 else 2930) else (if i < 903 then 2944 else 2945))) else (if i < 908 then (if i < 906 then (if i < 905 then 2947 else 2948) else (if i < 907 then 2949 else 2950)) else (if i < 910 then (if i < 909 then 2951 else 2961) else (if i < 911 then 2962 else 2963)))) else (if i < 920 then (if i < 916 then (if i < 914 then (if i < 913 then 2964 else 2965) else (if i < 915 then 2967 else 2983)) else (if i < 918 then (if i < 917 then 2997 else 2999) else (if i < 919 then 3000 else 3001))) else (if i < 924 then (if i < 922 then (if i < 921 then 3011 else 3013) else (if i < 923 then 3014 else 3015)) else (if i < 926 then (if i < 925 then 3025 else 3027) else (if i < 927 then 3028 else 3029)))))

private def rootValue_b29 (i : ℕ) : ℕ :=
  (if i < 944 then (if i < 936 then (if i < 932 then (if i < 930 then (if i < 929 then 3038 else 3048) else (if i < 931 then 3049 else 3050)) else (if i < 934 then (if i < 933 then 3051 else 3052) else (if i < 935 then 3053 else 3054))) else (if i < 940 then (if i < 938 then (if i < 937 then 3064 else 3065) else (if i < 939 then 3066 else 3067)) else (if i < 942 then (if i < 941 then 3068 else 3069) else (if i < 943 then 3070 else 3071)))) else (if i < 952 then (if i < 948 then (if i < 946 then (if i < 945 then 3080 else 3081) else (if i < 947 then 3082 else 3084)) else (if i < 950 then (if i < 949 then 3086 else 3096) else (if i < 951 then 3097 else 3098))) else (if i < 956 then (if i < 954 then (if i < 953 then 3100 else 3102) else (if i < 955 then 3103 else 3112)) else (if i < 958 then (if i < 957 then 3114 else 3115) else (if i < 959 then 3116 else 3117)))))

private def rootValue_b30 (i : ℕ) : ℕ :=
  (if i < 976 then (if i < 968 then (if i < 964 then (if i < 962 then (if i < 961 then 3118 else 3134) else (if i < 963 then 3148 else 3149)) else (if i < 966 then (if i < 965 then 3151 else 3152) else (if i < 967 then 3153 else 3154))) else (if i < 972 then (if i < 970 then (if i < 969 then 3155 else 3165) else (if i < 971 then 3166 else 3167)) else (if i < 974 then (if i < 973 then 3168 else 3169) else (if i < 975 then 3170 else 3171)))) else (if i < 984 then (if i < 980 then (if i < 978 then (if i < 977 then 3187 else 3200) else (if i < 979 then 3201 else 3202)) else (if i < 982 then (if i < 981 then 3203 else 3204) else (if i < 983 then 3205 else 3206))) else (if i < 988 then (if i < 986 then (if i < 985 then 3216 else 3217) else (if i < 987 then 3218 else 3219)) else (if i < 990 then (if i < 989 then 3220 else 3221) else (if i < 991 then 3222 else 3223)))))

private def rootValue_b31 (i : ℕ) : ℕ :=
  (if i < 1008 then (if i < 1000 then (if i < 996 then (if i < 994 then (if i < 993 then 3232 else 3233) else (if i < 995 then 3234 else 3236)) else (if i < 998 then (if i < 997 then 3238 else 3248) else (if i < 999 then 3249 else 3250))) else (if i < 1004 then (if i < 1002 then (if i < 1001 then 3252 else 3254) else (if i < 1003 then 3255 else 3264)) else (if i < 1006 then (if i < 1005 then 3266 else 3267) else (if i < 1007 then 3268 else 3269)))) else (if i < 1016 then (if i < 1012 then (if i < 1010 then (if i < 1009 then 3270 else 3286) else (if i < 1011 then 3300 else 3301)) else (if i < 1014 then (if i < 1013 then 3303 else 3304) else (if i < 1015 then 3305 else 3306))) else (if i < 1020 then (if i < 1018 then (if i < 1017 then 3307 else 3317) else (if i < 1019 then 3318 else 3319)) else (if i < 1022 then (if i < 1021 then 3320 else 3321) else (if i < 1023 then 3322 else 3323)))))

private def rootValue_b32 (i : ℕ) : ℕ :=
  (if i < 1040 then (if i < 1032 then (if i < 1028 then (if i < 1026 then (if i < 1025 then 3339 else 3352) else (if i < 1027 then 3354 else 3355)) else (if i < 1030 then (if i < 1029 then 3356 else 3357) else (if i < 1031 then 3358 else 3368))) else (if i < 1036 then (if i < 1034 then (if i < 1033 then 3369 else 3370) else (if i < 1035 then 3371 else 3372)) else (if i < 1038 then (if i < 1037 then 3373 else 3374) else (if i < 1039 then 3375 else 3384)))) else (if i < 1048 then (if i < 1044 then (if i < 1042 then (if i < 1041 then 3385 else 3386) else (if i < 1043 then 3388 else 3390)) else (if i < 1046 then (if i < 1045 then 3400 else 3401) else (if i < 1047 then 3402 else 3404))) else (if i < 1052 then (if i < 1050 then (if i < 1049 then 3406 else 3407) else (if i < 1051 then 3416 else 3418)) else (if i < 1054 then (if i < 1053 then 3419 else 3420) else (if i < 1055 then 3421 else 3422)))))

private def rootValue_b33 (i : ℕ) : ℕ :=
  (if i < 1072 then (if i < 1064 then (if i < 1060 then (if i < 1058 then (if i < 1057 then 3438 else 3452) else (if i < 1059 then 3453 else 3455)) else (if i < 1062 then (if i < 1061 then 3456 else 3457) else (if i < 1063 then 3458 else 3459))) else (if i < 1068 then (if i < 1066 then (if i < 1065 then 3469 else 3470) else (if i < 1067 then 3471 else 3472)) else (if i < 1070 then (if i < 1069 then 3473 else 3475) else (if i < 1071 then 3491 else 3505)))) else (if i < 1080 then (if i < 1076 then (if i < 1074 then (if i < 1073 then 3507 else 3508) else (if i < 1075 then 3509 else 3519)) else (if i < 1078 then (if i < 1077 then 3521 else 3522) else (if i < 1079 then 3523 else 3533))) else (if i < 1084 then (if i < 1082 then (if i < 1081 then 3535 else 3536) else (if i < 1083 then 3537 else 3546)) else (if i < 1086 then (if i < 1085 then 3556 else 3557) else (if i < 1087 then 3558 else 3559)))))

private def rootValue_b34 (i : ℕ) : ℕ :=
  (if i < 1104 then (if i < 1096 then (if i < 1092 then (if i < 1090 then (if i < 1089 then 3560 else 3561) else (if i < 1091 then 3562 else 3563)) else (if i < 1094 then (if i < 1093 then 3572 else 3573) else (if i < 1095 then 3574 else 3575))) else (if i < 1100 then (if i < 1098 then (if i < 1097 then 3576 else 3577) else (if i < 1099 then 3578 else 3579)) else (if i < 1102 then (if i < 1101 then 3588 else 3589) else (if i < 1103 then 3590 else 3592)))) else (if i < 1112 then (if i < 1108 then (if i < 1106 then (if i < 1105 then 3594 else 3604) else (if i < 1107 then 3605 else 3606)) else (if i < 1110 then (if i < 1109 then 3608 else 3610) else (if i < 1111 then 3611 else 3620))) else (if i < 1116 then (if i < 1114 then (if i < 1113 then 3622 else 3623) else (if i < 1115 then 3624 else 3625)) else (if i < 1118 then (if i < 1117 then 3626 else 3642) else (if i < 1119 then 3656 else 3657)))))

private def rootValue_b35 (i : ℕ) : ℕ :=
  (if i < 1136 then (if i < 1128 then (if i < 1124 then (if i < 1122 then (if i < 1121 then 3659 else 3660) else (if i < 1123 then 3661 else 3662)) else (if i < 1126 then (if i < 1125 then 3663 else 3673) else (if i < 1127 then 3674 else 3675))) else (if i < 1132 then (if i < 1130 then (if i < 1129 then 3676 else 3677) else (if i < 1131 then 3678 else 3679)) else (if i < 1134 then (if i < 1133 then 3695 else 3708) else (if i < 1135 then 3710 else 3711)))) else (if i < 1144 then (if i < 1140 then (if i < 1138 then (if i < 1137 then 3712 else 3713) else (if i < 1139 then 3714 else 3715)) else (if i < 1142 then (if i < 1141 then 3724 else 3725) else (if i < 1143 then 3726 else 3727))) else (if i < 1148 then (if i < 1146 then (if i < 1145 then 3728 else 3729) else (if i < 1147 then 3730 else 3731)) else (if i < 1150 then (if i < 1149 then 3740 else 3741) else (if i < 1151 then 3742 else 3744)))))

private def rootValue_b36 (i : ℕ) : ℕ :=
  (if i < 1168 then (if i < 1160 then (if i < 1156 then (if i < 1154 then (if i < 1153 then 3746 else 3756) else (if i < 1155 then 3757 else 3758)) else (if i < 1158 then (if i < 1157 then 3760 else 3762) else (if i < 1159 then 3763 else 3772))) else (if i < 1164 then (if i < 1162 then (if i < 1161 then 3774 else 3775) else (if i < 1163 then 3776 else 3777)) else (if i < 1166 then (if i < 1165 then 3778 else 3794) else (if i < 1167 then 3808 else 3809)))) else (if i < 1176 then (if i < 1172 then (if i < 1170 then (if i < 1169 then 3811 else 3812) else (if i < 1171 then 3813 else 3814)) else (if i < 1174 then (if i < 1173 then 3815 else 3825) else (if i < 1175 then 3826 else 3827))) else (if i < 1180 then (if i < 1178 then (if i < 1177 then 3828 else 3829) else (if i < 1179 then 3830 else 3831)) else (if i < 1182 then (if i < 1181 then 3847 else 3860) else (if i < 1183 then 3861 else 3862)))))

private def rootValue_b37 (i : ℕ) : ℕ :=
  (if i < 1200 then (if i < 1192 then (if i < 1188 then (if i < 1186 then (if i < 1185 then 3863 else 3864) else (if i < 1187 then 3865 else 3866)) else (if i < 1190 then (if i < 1189 then 3876 else 3877) else (if i < 1191 then 3878 else 3879))) else (if i < 1196 then (if i < 1194 then (if i < 1193 then 3880 else 3881) else (if i < 1195 then 3882 else 3883)) else (if i < 1198 then (if i < 1197 then 3892 else 3893) else (if i < 1199 then 3894 else 3896)))) else (if i < 1208 then (if i < 1204 then (if i < 1202 then (if i < 1201 then 3898 else 3908) else (if i < 1203 then 3909 else 3910)) else (if i < 1206 then (if i < 1205 then 3912 else 3914) else (if i < 1207 then 3915 else 3924))) else (if i < 1212 then (if i < 1210 then (if i < 1209 then 3926 else 3927) else (if i < 1211 then 3928 else 3929)) else (if i < 1214 then (if i < 1213 then 3930 else 3946) else (if i < 1215 then 3960 else 3961)))))

private def rootValue_b38 (i : ℕ) : ℕ :=
  (if i < 1232 then (if i < 1224 then (if i < 1220 then (if i < 1218 then (if i < 1217 then 3963 else 3964) else (if i < 1219 then 3965 else 3966)) else (if i < 1222 then (if i < 1221 then 3967 else 3977) else (if i < 1223 then 3978 else 3979))) else (if i < 1228 then (if i < 1226 then (if i < 1225 then 3980 else 3981) else (if i < 1227 then 3983 else 3999)) else (if i < 1230 then (if i < 1229 then 4013 else 4015) else (if i < 1231 then 4016 else 4017)))) else (if i < 1240 then (if i < 1236 then (if i < 1234 then (if i < 1233 then 4027 else 4029) else (if i < 1235 then 4030 else 4031)) else (if i < 1238 then (if i < 1237 then 4041 else 4043) else (if i < 1239 then 4044 else 4045))) else (if i < 1244 then (if i < 1242 then (if i < 1241 then 4054 else 4064) else (if i < 1243 then 4065 else 4066)) else (if i < 1246 then (if i < 1245 then 4067 else 4068) else (if i < 1247 then 4069 else 4070)))))

private def rootValue_b39 (i : ℕ) : ℕ :=
  (if i < 1264 then (if i < 1256 then (if i < 1252 then (if i < 1250 then (if i < 1249 then 4080 else 4081) else (if i < 1251 then 4082 else 4083)) else (if i < 1254 then (if i < 1253 then 4084 else 4085) else (if i < 1255 then 4086 else 4087))) else (if i < 1260 then (if i < 1258 then (if i < 1257 then 4096 else 4097) else (if i < 1259 then 4098 else 4100)) else (if i < 1262 then (if i < 1261 then 4102 else 4112) else (if i < 1263 then 4113 else 4114)))) else (if i < 1272 then (if i < 1268 then (if i < 1266 then (if i < 1265 then 4116 else 4118) else (if i < 1267 then 4119 else 4128)) else (if i < 1270 then (if i < 1269 then 4130 else 4131) else (if i < 1271 then 4132 else 4133))) else (if i < 1276 then (if i < 1274 then (if i < 1273 then 4134 else 4150) else (if i < 1275 then 4164 else 4165)) else (if i < 1278 then (if i < 1277 then 4167 else 4168) else (if i < 1279 then 4169 else 4170)))))

private def rootValue_b40 (i : ℕ) : ℕ :=
  (if i < 1296 then (if i < 1288 then (if i < 1284 then (if i < 1282 then (if i < 1281 then 4171 else 4181) else (if i < 1283 then 4182 else 4183)) else (if i < 1286 then (if i < 1285 then 4184 else 4185) else (if i < 1287 then 4186 else 4187))) else (if i < 1292 then (if i < 1290 then (if i < 1289 then 4203 else 4216) else (if i < 1291 then 4218 else 4219)) else (if i < 1294 then (if i < 1293 then 4220 else 4221) else (if i < 1295 then 4222 else 4232)))) else (if i < 1304 then (if i < 1300 then (if i < 1298 then (if i < 1297 then 4233 else 4234) else (if i < 1299 then 4235 else 4236)) else (if i < 1302 then (if i < 1301 then 4237 else 4238) else (if i < 1303 then 4239 else 4248))) else (if i < 1308 then (if i < 1306 then (if i < 1305 then 4249 else 4250) else (if i < 1307 then 4252 else 4254)) else (if i < 1310 then (if i < 1309 then 4264 else 4265) else (if i < 1311 then 4266 else 4268)))))

private def rootValue_b41 (i : ℕ) : ℕ :=
  (if i < 1328 then (if i < 1320 then (if i < 1316 then (if i < 1314 then (if i < 1313 then 4270 else 4271) else (if i < 1315 then 4280 else 4282)) else (if i < 1318 then (if i < 1317 then 4283 else 4284) else (if i < 1319 then 4285 else 4286))) else (if i < 1324 then (if i < 1322 then (if i < 1321 then 4302 else 4316) else (if i < 1323 then 4317 else 4319)) else (if i < 1326 then (if i < 1325 then 4320 else 4321) else (if i < 1327 then 4322 else 4323)))) else (if i < 1336 then (if i < 1332 then (if i < 1330 then (if i < 1329 then 4333 else 4334) else (if i < 1331 then 4335 else 4336)) else (if i < 1334 then (if i < 1333 then 4337 else 4338) else (if i < 1335 then 4339 else 4355))) else (if i < 1340 then (if i < 1338 then (if i < 1337 then 4368 else 4370) else (if i < 1339 then 4371 else 4372)) else (if i < 1342 then (if i < 1341 then 4373 else 4374) else (if i < 1343 then 4384 else 4385)))))

private def rootValue_b42 (i : ℕ) : ℕ :=
  (if i < 1360 then (if i < 1352 then (if i < 1348 then (if i < 1346 then (if i < 1345 then 4386 else 4387) else (if i < 1347 then 4388 else 4389)) else (if i < 1350 then (if i < 1349 then 4390 else 4391) else (if i < 1351 then 4400 else 4401))) else (if i < 1356 then (if i < 1354 then (if i < 1353 then 4402 else 4404) else (if i < 1355 then 4406 else 4416)) else (if i < 1358 then (if i < 1357 then 4417 else 4418) else (if i < 1359 then 4420 else 4422)))) else (if i < 1368 then (if i < 1364 then (if i < 1362 then (if i < 1361 then 4423 else 4432) else (if i < 1363 then 4434 else 4435)) else (if i < 1366 then (if i < 1365 then 4436 else 4437) else (if i < 1367 then 4438 else 4454))) else (if i < 1372 then (if i < 1370 then (if i < 1369 then 4468 else 4469) else (if i < 1371 then 4471 else 4472)) else (if i < 1374 then (if i < 1373 then 4473 else 4474) else (if i < 1375 then 4475 else 4485)))))

private def rootValue_b43 (i : ℕ) : ℕ :=
  (if i < 1392 then (if i < 1384 then (if i < 1380 then (if i < 1378 then (if i < 1377 then 4486 else 4487) else (if i < 1379 then 4488 else 4489)) else (if i < 1382 then (if i < 1381 then 4491 else 4507) else (if i < 1383 then 4521 else 4523))) else (if i < 1388 then (if i < 1386 then (if i < 1385 then 4525 else 4535) else (if i < 1387 then 4537 else 4538)) else (if i < 1390 then (if i < 1389 then 4539 else 4549) else (if i < 1391 then 4551 else 4553)))) else (if i < 1400 then (if i < 1396 then (if i < 1394 then (if i < 1393 then 4562 else 4572) else (if i < 1395 then 4574 else 4575)) else (if i < 1398 then (if i < 1397 then 4576 else 4577) else (if i < 1399 then 4578 else 4588))) else (if i < 1404 then (if i < 1402 then (if i < 1401 then 4589 else 4590) else (if i < 1403 then 4591 else 4592)) else (if i < 1406 then (if i < 1405 then 4593 else 4594) else (if i < 1407 then 4595 else 4604)))))

private def rootValue_b44 (i : ℕ) : ℕ :=
  (if i < 1424 then (if i < 1416 then (if i < 1412 then (if i < 1410 then (if i < 1409 then 4605 else 4606) else (if i < 1411 then 4608 else 4610)) else (if i < 1414 then (if i < 1413 then 4620 else 4621) else (if i < 1415 then 4622 else 4624))) else (if i < 1420 then (if i < 1418 then (if i < 1417 then 4626 else 4627) else (if i < 1419 then 4636 else 4638)) else (if i < 1422 then (if i < 1421 then 4639 else 4640) else (if i < 1423 then 4641 else 4642)))) else (if i < 1432 then (if i < 1428 then (if i < 1426 then (if i < 1425 then 4658 else 4672) else (if i < 1427 then 4673 else 4675)) else (if i < 1430 then (if i < 1429 then 4676 else 4677) else (if i < 1431 then 4678 else 4679))) else (if i < 1436 then (if i < 1434 then (if i < 1433 then 4689 else 4690) else (if i < 1435 then 4691 else 4692)) else (if i < 1438 then (if i < 1437 then 4693 else 4694) else (if i < 1439 then 4695 else 4711)))))

private def rootValue_b45 (i : ℕ) : ℕ :=
  (if i < 1456 then (if i < 1448 then (if i < 1444 then (if i < 1442 then (if i < 1441 then 4724 else 4726) else (if i < 1443 then 4727 else 4728)) else (if i < 1446 then (if i < 1445 then 4729 else 4730) else (if i < 1447 then 4740 else 4741))) else (if i < 1452 then (if i < 1450 then (if i < 1449 then 4742 else 4743) else (if i < 1451 then 4744 else 4745)) else (if i < 1454 then (if i < 1453 then 4746 else 4747) else (if i < 1455 then 4756 else 4757)))) else (if i < 1464 then (if i < 1460 then (if i < 1458 then (if i < 1457 then 4758 else 4760) else (if i < 1459 then 4762 else 4772)) else (if i < 1462 then (if i < 1461 then 4773 else 4774) else (if i < 1463 then 4776 else 4778))) else (if i < 1468 then (if i < 1466 then (if i < 1465 then 4779 else 4788) else (if i < 1467 then 4790 else 4791)) else (if i < 1470 then (if i < 1469 then 4792 else 4793) else (if i < 1471 then 4794 else 4810)))))

private def rootValue_b46 (i : ℕ) : ℕ :=
  (if i < 1488 then (if i < 1480 then (if i < 1476 then (if i < 1474 then (if i < 1473 then 4824 else 4825) else (if i < 1475 then 4827 else 4828)) else (if i < 1478 then (if i < 1477 then 4829 else 4830) else (if i < 1479 then 4831 else 4841))) else (if i < 1484 then (if i < 1482 then (if i < 1481 then 4842 else 4843) else (if i < 1483 then 4844 else 4845)) else (if i < 1486 then (if i < 1485 then 4846 else 4847) else (if i < 1487 then 4863 else 4876)))) else (if i < 1496 then (if i < 1492 then (if i < 1490 then (if i < 1489 then 4878 else 4879) else (if i < 1491 then 4880 else 4881)) else (if i < 1494 then (if i < 1493 then 4882 else 4892) else (if i < 1495 then 4893 else 4894))) else (if i < 1500 then (if i < 1498 then (if i < 1497 then 4895 else 4896) else (if i < 1499 then 4897 else 4898)) else (if i < 1502 then (if i < 1501 then 4899 else 4908) else (if i < 1503 then 4909 else 4910)))))

private def rootValue_b47 (i : ℕ) : ℕ :=
  (if i < 1520 then (if i < 1512 then (if i < 1508 then (if i < 1506 then (if i < 1505 then 4912 else 4914) else (if i < 1507 then 4924 else 4925)) else (if i < 1510 then (if i < 1509 then 4926 else 4928) else (if i < 1511 then 4930 else 4931))) else (if i < 1516 then (if i < 1514 then (if i < 1513 then 4940 else 4942) else (if i < 1515 then 4943 else 4944)) else (if i < 1518 then (if i < 1517 then 4945 else 4946) else (if i < 1519 then 4962 else 4976)))) else (if i < 1528 then (if i < 1524 then (if i < 1522 then (if i < 1521 then 4977 else 4979) else (if i < 1523 then 4980 else 4981)) else (if i < 1526 then (if i < 1525 then 4982 else 4983) else (if i < 1527 then 4993 else 4994))) else (if i < 1532 then (if i < 1530 then (if i < 1529 then 4995 else 4996) else (if i < 1531 then 4997 else 4999)) else (if i < 1534 then (if i < 1533 then 5015 else 5029) else (if i < 1535 then 5031 else 5033)))))

private def rootValue_b48 (i : ℕ) : ℕ :=
  (if i < 1552 then (if i < 1544 then (if i < 1540 then (if i < 1538 then (if i < 1537 then 5043 else 5045) else (if i < 1539 then 5046 else 5047)) else (if i < 1542 then (if i < 1541 then 5057 else 5059) else (if i < 1543 then 5061 else 5070))) else (if i < 1548 then (if i < 1546 then (if i < 1545 then 5080 else 5081) else (if i < 1547 then 5083 else 5085)) else (if i < 1550 then (if i < 1549 then 5094 else 5096) else (if i < 1551 then 5103 else 5107)))) else (if i < 1560 then (if i < 1556 then (if i < 1554 then (if i < 1553 then 5109 else 5114) else (if i < 1555 then 5119 else 5121)) else (if i < 1558 then (if i < 1557 then 5126 else 5131) else (if i < 1559 then 5133 else 5143))) else (if i < 1564 then (if i < 1562 then (if i < 1561 then 5145 else 5155) else (if i < 1563 then 5157 else 5167)) else (if i < 1566 then (if i < 1565 then 5169 else 5179) else (if i < 1567 then 5181 else 5191)))))

private def rootValue_b49 (i : ℕ) : ℕ :=
  (if i < 1572 then (if i < 1570 then (if i < 1569 then 5193 else 5203) else (if i < 1571 then 5205 else 5215)) else (if i < 1574 then (if i < 1573 then 5217 else 5227) else (if i < 1575 then 5229 else 5263)))

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

private def rootValue_n0_12 (i : ℕ) : ℕ := if i < 800 then rootValue_b24 i else rootValue_b25 i

private def rootValue_n0_13 (i : ℕ) : ℕ := if i < 864 then rootValue_b26 i else rootValue_b27 i

private def rootValue_n0_14 (i : ℕ) : ℕ := if i < 928 then rootValue_b28 i else rootValue_b29 i

private def rootValue_n0_15 (i : ℕ) : ℕ := if i < 992 then rootValue_b30 i else rootValue_b31 i

private def rootValue_n0_16 (i : ℕ) : ℕ := if i < 1056 then rootValue_b32 i else rootValue_b33 i

private def rootValue_n0_17 (i : ℕ) : ℕ := if i < 1120 then rootValue_b34 i else rootValue_b35 i

private def rootValue_n0_18 (i : ℕ) : ℕ := if i < 1184 then rootValue_b36 i else rootValue_b37 i

private def rootValue_n0_19 (i : ℕ) : ℕ := if i < 1248 then rootValue_b38 i else rootValue_b39 i

private def rootValue_n0_20 (i : ℕ) : ℕ := if i < 1312 then rootValue_b40 i else rootValue_b41 i

private def rootValue_n0_21 (i : ℕ) : ℕ := if i < 1376 then rootValue_b42 i else rootValue_b43 i

private def rootValue_n0_22 (i : ℕ) : ℕ := if i < 1440 then rootValue_b44 i else rootValue_b45 i

private def rootValue_n0_23 (i : ℕ) : ℕ := if i < 1504 then rootValue_b46 i else rootValue_b47 i

private def rootValue_n0_24 (i : ℕ) : ℕ := if i < 1568 then rootValue_b48 i else rootValue_b49 i

private def rootValue_n1_0 (i : ℕ) : ℕ := if i < 64 then rootValue_n0_0 i else rootValue_n0_1 i

private def rootValue_n1_1 (i : ℕ) : ℕ := if i < 192 then rootValue_n0_2 i else rootValue_n0_3 i

private def rootValue_n1_2 (i : ℕ) : ℕ := if i < 320 then rootValue_n0_4 i else rootValue_n0_5 i

private def rootValue_n1_3 (i : ℕ) : ℕ := if i < 448 then rootValue_n0_6 i else rootValue_n0_7 i

private def rootValue_n1_4 (i : ℕ) : ℕ := if i < 576 then rootValue_n0_8 i else rootValue_n0_9 i

private def rootValue_n1_5 (i : ℕ) : ℕ := if i < 704 then rootValue_n0_10 i else rootValue_n0_11 i

private def rootValue_n1_6 (i : ℕ) : ℕ := if i < 832 then rootValue_n0_12 i else rootValue_n0_13 i

private def rootValue_n1_7 (i : ℕ) : ℕ := if i < 960 then rootValue_n0_14 i else rootValue_n0_15 i

private def rootValue_n1_8 (i : ℕ) : ℕ := if i < 1088 then rootValue_n0_16 i else rootValue_n0_17 i

private def rootValue_n1_9 (i : ℕ) : ℕ := if i < 1216 then rootValue_n0_18 i else rootValue_n0_19 i

private def rootValue_n1_10 (i : ℕ) : ℕ := if i < 1344 then rootValue_n0_20 i else rootValue_n0_21 i

private def rootValue_n1_11 (i : ℕ) : ℕ := if i < 1472 then rootValue_n0_22 i else rootValue_n0_23 i

private def rootValue_n2_0 (i : ℕ) : ℕ := if i < 128 then rootValue_n1_0 i else rootValue_n1_1 i

private def rootValue_n2_1 (i : ℕ) : ℕ := if i < 384 then rootValue_n1_2 i else rootValue_n1_3 i

private def rootValue_n2_2 (i : ℕ) : ℕ := if i < 640 then rootValue_n1_4 i else rootValue_n1_5 i

private def rootValue_n2_3 (i : ℕ) : ℕ := if i < 896 then rootValue_n1_6 i else rootValue_n1_7 i

private def rootValue_n2_4 (i : ℕ) : ℕ := if i < 1152 then rootValue_n1_8 i else rootValue_n1_9 i

private def rootValue_n2_5 (i : ℕ) : ℕ := if i < 1408 then rootValue_n1_10 i else rootValue_n1_11 i

private def rootValue_n3_0 (i : ℕ) : ℕ := if i < 256 then rootValue_n2_0 i else rootValue_n2_1 i

private def rootValue_n3_1 (i : ℕ) : ℕ := if i < 768 then rootValue_n2_2 i else rootValue_n2_3 i

private def rootValue_n3_2 (i : ℕ) : ℕ := if i < 1280 then rootValue_n2_4 i else rootValue_n2_5 i

private def rootValue_n4_0 (i : ℕ) : ℕ := if i < 512 then rootValue_n3_0 i else rootValue_n3_1 i

private def rootValue_n4_1 (i : ℕ) : ℕ := if i < 1536 then rootValue_n3_2 i else rootValue_n0_24 i

private def rootValue_n5_0 (i : ℕ) : ℕ := if i < 1024 then rootValue_n4_0 i else rootValue_n4_1 i

def rootValue (i : ℕ) : ℕ := rootValue_n5_0 i

end PlanarHom.ColoringMacroFaces.FanFramed
