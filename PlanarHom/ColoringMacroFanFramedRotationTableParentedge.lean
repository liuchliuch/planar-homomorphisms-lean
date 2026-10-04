import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.FanFramed
private def parentEdgeValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 2624) else (if i < 3 then 2627 else 76)) else (if i < 6 then (if i < 5 then 3 else 584) else (if i < 7 then 511 else 762))) else (if i < 12 then (if i < 10 then (if i < 9 then 1346 else 1273) else (if i < 11 then 1854 else 1781)) else (if i < 14 then (if i < 13 then 2108 else 251) else (if i < 15 then 19 else 1)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 252 else 9) else (if i < 19 then 244 else 242)) else (if i < 22 then (if i < 21 then 2 else 11) else (if i < 23 then 10 else 7))) else (if i < 28 then (if i < 26 then (if i < 25 then 15 else 23) else (if i < 27 then 40 else 49)) else (if i < 30 then (if i < 29 then 44 else 35) else (if i < 31 then 32 else 46)))))

private def parentEdgeValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 24 else 33) else (if i < 35 then 29 else 36)) else (if i < 38 then (if i < 37 then 51 else 52) else (if i < 39 then 69 else 74))) else (if i < 44 then (if i < 42 then (if i < 41 then 67 else 71) else (if i < 43 then 50 else 60)) else (if i < 46 then (if i < 45 then 56 else 65) else (if i < 47 then 250 else 237)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 95 else 235) else (if i < 51 then 93 else 79)) else (if i < 54 then (if i < 53 then 87 else 77) else (if i < 55 then 84 else 85))) else (if i < 60 then (if i < 58 then (if i < 57 then 81 else 89) else (if i < 59 then 96 else 101)) else (if i < 62 then (if i < 61 then 102 else 119) else (if i < 63 then 124 else 117)))))

private def parentEdgeValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 121 else 100) else (if i < 67 then 109 else 106)) else (if i < 70 then (if i < 69 then 112 else 142) else (if i < 71 then 151 else 146))) else (if i < 76 then (if i < 74 then (if i < 73 then 137 else 134) else (if i < 75 then 148 else 144)) else (if i < 78 then (if i < 77 then 135 else 133) else (if i < 79 then 138 else 253)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 171 else 152) else (if i < 83 then 169 else 170)) else (if i < 86 then (if i < 85 then 155 else 236) else (if i < 87 then 153 else 160))) else (if i < 92 then (if i < 90 then (if i < 89 then 161 else 156) else (if i < 91 then 165 else 175)) else (if i < 94 then (if i < 93 then 192 else 178) else (if i < 95 then 196 else 187)))))

private def parentEdgeValue_b3 (i : ℕ) : ℕ :=
  (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 184 else 198) else (if i < 99 then 176 else 185)) else (if i < 102 then (if i < 101 then 182 else 188) else (if i < 103 then 203 else 204))) else (if i < 108 then (if i < 106 then (if i < 105 then 221 else 213) else (if i < 107 then 219 else 223)) else (if i < 110 then (if i < 109 then 202 else 211) else (if i < 111 then 208 else 214)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 232 else 241) else (if i < 115 then 245 else 506)) else (if i < 118 then (if i < 117 then 273 else 254) else (if i < 119 then 271 else 272))) else (if i < 124 then (if i < 122 then (if i < 121 then 257 else 497) else (if i < 123 then 255 else 262)) else (if i < 126 then (if i < 125 then 263 else 258) else (if i < 127 then 267 else 277)))))

private def parentEdgeValue_b4 (i : ℕ) : ℕ :=
  (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 294 else 280) else (if i < 131 then 298 else 289)) else (if i < 134 then (if i < 133 then 286 else 300) else (if i < 135 then 278 else 287))) else (if i < 140 then (if i < 138 then (if i < 137 then 284 else 290) else (if i < 139 then 305 else 306)) else (if i < 142 then (if i < 141 then 323 else 315) else (if i < 143 then 321 else 325)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 304 else 313) else (if i < 147 then 310 else 316)) else (if i < 150 then (if i < 149 then 504 else 491) else (if i < 151 then 330 else 489))) else (if i < 156 then (if i < 154 then (if i < 153 then 348 else 333) else (if i < 155 then 483 else 331)) else (if i < 158 then (if i < 157 then 338 else 339) else (if i < 159 then 334 else 343)))))

private def parentEdgeValue_b5 (i : ℕ) : ℕ :=
  (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 353 else 370) else (if i < 163 then 356 else 374)) else (if i < 166 then (if i < 165 then 365 else 362) else (if i < 167 then 376 else 354))) else (if i < 172 then (if i < 170 then (if i < 169 then 363 else 360) else (if i < 171 then 366 else 381)) else (if i < 174 then (if i < 173 then 382 else 399) else (if i < 175 then 391 else 388)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 401 else 380) else (if i < 179 then 389 else 386)) else (if i < 182 then (if i < 181 then 392 else 507) else (if i < 183 then 498 else 406))) else (if i < 188 then (if i < 186 then (if i < 185 then 496 else 424) else (if i < 187 then 409 else 490)) else (if i < 190 then (if i < 189 then 407 else 414) else (if i < 191 then 415 else 410)))))

private def parentEdgeValue_b6 (i : ℕ) : ℕ :=
  (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 419 else 429) else (if i < 195 then 446 else 432)) else (if i < 198 then (if i < 197 then 450 else 441) else (if i < 199 then 438 else 452))) else (if i < 204 then (if i < 202 then (if i < 201 then 430 else 439) else (if i < 203 then 436 else 442)) else (if i < 206 then (if i < 205 then 457 else 458) else (if i < 207 then 475 else 467)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 464 else 477) else (if i < 211 then 456 else 465)) else (if i < 214 then (if i < 213 then 462 else 468) else (if i < 215 then 488 else 495))) else (if i < 220 then (if i < 218 then (if i < 217 then 502 else 759) else (if i < 219 then 738 else 509)) else (if i < 222 then (if i < 221 then 760 else 525) else (if i < 223 then 752 else 750)))))

private def parentEdgeValue_b7 (i : ℕ) : ℕ :=
  (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 510 else 519) else (if i < 227 then 518 else 515)) else (if i < 230 then (if i < 229 then 523 else 529) else (if i < 231 then 548 else 534))) else (if i < 236 then (if i < 234 then (if i < 233 then 552 else 543) else (if i < 235 then 540 else 554)) else (if i < 238 then (if i < 237 then 532 else 541) else (if i < 239 then 538 else 544)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 559 else 583) else (if i < 243 then 577 else 582)) else (if i < 246 then (if i < 245 then 566 else 579) else (if i < 247 then 561 else 568))) else (if i < 252 then (if i < 250 then (if i < 249 then 565 else 573) else (if i < 251 then 758 else 2571)) else (if i < 254 then (if i < 253 then 603 else 600) else (if i < 255 then 601 else 587)))))

private def parentEdgeValue_b8 (i : ℕ) : ℕ :=
  (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 595 else 585) else (if i < 259 then 592 else 593)) else (if i < 262 then (if i < 261 then 589 else 597) else (if i < 263 then 604 else 609))) else (if i < 268 then (if i < 266 then (if i < 265 then 610 else 627) else (if i < 267 then 632 else 625)) else (if i < 270 then (if i < 269 then 629 else 608) else (if i < 271 then 617 else 614)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 620 else 650) else (if i < 275 then 659 else 654)) else (if i < 278 then (if i < 277 then 645 else 642) else (if i < 279 then 656 else 652))) else (if i < 284 then (if i < 282 then (if i < 281 then 643 else 641) else (if i < 283 then 646 else 761)) else (if i < 286 then (if i < 285 then 679 else 660) else (if i < 287 then 677 else 678)))))

private def parentEdgeValue_b9 (i : ℕ) : ℕ :=
  (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 2572 else 744) else (if i < 291 then 662 else 708)) else (if i < 294 then (if i < 293 then 670 else 667) else (if i < 295 then 675 else 683))) else (if i < 300 then (if i < 298 then (if i < 297 then 700 else 703) else (if i < 299 then 704 else 695)) else (if i < 302 then (if i < 301 then 692 else 706) else (if i < 303 then 684 else 693)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 689 else 696) else (if i < 307 then 711 else 712)) else (if i < 310 then (if i < 309 then 729 else 734) else (if i < 311 then 727 else 731))) else (if i < 316 then (if i < 314 then (if i < 313 then 710 else 719) else (if i < 315 then 716 else 723)) else (if i < 318 then (if i < 317 then 742 else 749) else (if i < 319 then 753 else 1014)))))

private def parentEdgeValue_b10 (i : ℕ) : ℕ :=
  (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 992 else 781) else (if i < 323 then 990 else 779)) else (if i < 326 then (if i < 325 then 765 else 773) else (if i < 327 then 763 else 770))) else (if i < 332 then (if i < 330 then (if i < 329 then 771 else 767) else (if i < 331 then 775 else 782)) else (if i < 334 then (if i < 333 then 787 else 788) else (if i < 335 then 805 else 810)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 803 else 807) else (if i < 339 then 786 else 795)) else (if i < 342 then (if i < 341 then 792 else 798) else (if i < 343 then 828 else 837))) else (if i < 348 then (if i < 346 then (if i < 345 then 832 else 823) else (if i < 347 then 820 else 834)) else (if i < 350 then (if i < 349 then 830 else 821) else (if i < 351 then 819 else 824)))))

private def parentEdgeValue_b11 (i : ℕ) : ℕ :=
  (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 913 else 857) else (if i < 355 then 838 else 855)) else (if i < 358 then (if i < 357 then 856 else 841) else (if i < 359 then 991 else 839))) else (if i < 364 then (if i < 362 then (if i < 361 then 846 else 847) else (if i < 363 then 842 else 851)) else (if i < 366 then (if i < 365 then 861 else 878) else (if i < 367 then 864 else 882)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 873 else 870) else (if i < 371 then 884 else 862)) else (if i < 374 then (if i < 373 then 871 else 868) else (if i < 375 then 874 else 889))) else (if i < 380 then (if i < 378 then (if i < 377 then 890 else 907) else (if i < 379 then 899 else 905)) else (if i < 382 then (if i < 381 then 909 else 888) else (if i < 383 then 897 else 894)))))

private def parentEdgeValue_b12 (i : ℕ) : ℕ :=
  (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 900 else 1015) else (if i < 387 then 933 else 914)) else (if i < 390 then (if i < 389 then 931 else 932) else (if i < 391 then 999 else 997))) else (if i < 396 then (if i < 394 then (if i < 393 then 916 else 925) else (if i < 395 then 924 else 918)) else (if i < 398 then (if i < 397 then 929 else 937) else (if i < 399 then 954 else 940)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 958 else 949) else (if i < 403 then 946 else 960)) else (if i < 406 then (if i < 405 then 938 else 947) else (if i < 407 then 944 else 950))) else (if i < 412 then (if i < 410 then (if i < 409 then 965 else 966) else (if i < 411 then 983 else 988)) else (if i < 414 then (if i < 413 then 981 else 985) else (if i < 415 then 964 else 973)))))

private def parentEdgeValue_b13 (i : ℕ) : ℕ :=
  (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 970 else 976) else (if i < 419 then 996 else 1000)) else (if i < 422 then (if i < 421 then 1007 else 1268) else (if i < 423 then 1246 else 1016))) else (if i < 428 then (if i < 426 then (if i < 425 then 1244 else 1034) else (if i < 427 then 1019 else 1259)) else (if i < 430 then (if i < 429 then 1017 else 1024) else (if i < 431 then 1025 else 1020)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 1029 else 1036) else (if i < 435 then 1056 else 1042)) else (if i < 438 then (if i < 437 then 1060 else 1051) else (if i < 439 then 1048 else 1062))) else (if i < 444 then (if i < 442 then (if i < 441 then 1040 else 1049) else (if i < 443 then 1046 else 1052)) else (if i < 446 then (if i < 445 then 1067 else 1068) else (if i < 447 then 1086 else 1077)))))

private def parentEdgeValue_b14 (i : ℕ) : ℕ :=
  (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 1074 else 1088) else (if i < 451 then 1066 else 1075)) else (if i < 454 then (if i < 453 then 1072 else 1078) else (if i < 455 then 1167 else 2589))) else (if i < 460 then (if i < 458 then (if i < 457 then 1092 else 1108) else (if i < 459 then 1110 else 1095)) else (if i < 462 then (if i < 461 then 1245 else 1093) else (if i < 463 then 1100 else 1101)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 1096 else 1105) else (if i < 467 then 1115 else 1132)) else (if i < 470 then (if i < 469 then 1118 else 1136) else (if i < 471 then 1127 else 1124))) else (if i < 476 then (if i < 474 then (if i < 473 then 1138 else 1116) else (if i < 475 then 1125 else 1122)) else (if i < 478 then (if i < 477 then 1128 else 1143) else (if i < 479 then 1144 else 1161)))))

private def parentEdgeValue_b15 (i : ℕ) : ℕ :=
  (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 1153 else 1150) else (if i < 483 then 1163 else 1142)) else (if i < 486 then (if i < 485 then 1151 else 1148) else (if i < 487 then 1154 else 1269))) else (if i < 492 then (if i < 490 then (if i < 489 then 1187 else 1168) else (if i < 491 then 1185 else 1186)) else (if i < 494 then (if i < 493 then 1171 else 1252) else (if i < 495 then 1169 else 1176)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 1177 else 1172) else (if i < 499 then 1181 else 1191)) else (if i < 502 then (if i < 501 then 1208 else 1194) else (if i < 503 then 1212 else 1203))) else (if i < 508 then (if i < 506 then (if i < 505 then 1200 else 1214) else (if i < 507 then 1192 else 1201)) else (if i < 510 then (if i < 509 then 1198 else 1204) else (if i < 511 then 1219 else 1220)))))

private def parentEdgeValue_b16 (i : ℕ) : ℕ :=
  (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 1237 else 1229) else (if i < 515 then 1235 else 1239)) else (if i < 518 then (if i < 517 then 1218 else 1227) else (if i < 519 then 1224 else 1230))) else (if i < 524 then (if i < 522 then (if i < 521 then 1250 else 1254) else (if i < 523 then 1264 else 1521)) else (if i < 526 then (if i < 525 then 1289 else 1271) else (if i < 527 then 1522 else 1288)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 2578 else 1513) else (if i < 531 then 1272 else 1318)) else (if i < 534 then (if i < 533 then 1280 else 1277) else (if i < 535 then 1285 else 1293))) else (if i < 540 then (if i < 538 then (if i < 537 then 1310 else 1313) else (if i < 539 then 1314 else 1305)) else (if i < 542 then (if i < 541 then 1302 else 1316) else (if i < 543 then 1294 else 1303)))))

private def parentEdgeValue_b17 (i : ℕ) : ℕ :=
  (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then 1299 else 1306) else (if i < 547 then 1321 else 1322)) else (if i < 550 then (if i < 549 then 1339 else 1344) else (if i < 551 then 1337 else 1341))) else (if i < 556 then (if i < 554 then (if i < 553 then 1320 else 1330) else (if i < 555 then 1326 else 1335)) else (if i < 558 then (if i < 557 then 1520 else 1507) else (if i < 559 then 1365 else 1505)))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then 1363 else 1349) else (if i < 563 then 1357 else 1347)) else (if i < 566 then (if i < 565 then 1354 else 1355) else (if i < 567 then 1351 else 1359))) else (if i < 572 then (if i < 570 then (if i < 569 then 1366 else 1371) else (if i < 571 then 1372 else 1389)) else (if i < 574 then (if i < 573 then 1394 else 1387) else (if i < 575 then 1391 else 1370)))))

private def parentEdgeValue_b18 (i : ℕ) : ℕ :=
  (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then 1379 else 1376) else (if i < 579 then 1382 else 1412)) else (if i < 582 then (if i < 581 then 1421 else 1416) else (if i < 583 then 1407 else 1404))) else (if i < 588 then (if i < 586 then (if i < 585 then 1418 else 1414) else (if i < 587 then 1405 else 1403)) else (if i < 590 then (if i < 589 then 1408 else 1523) else (if i < 591 then 2577 else 1422)))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then 1438 else 1440) else (if i < 595 then 1425 else 1506)) else (if i < 598 then (if i < 597 then 1423 else 1430) else (if i < 599 then 1431 else 1426))) else (if i < 604 then (if i < 602 then (if i < 601 then 1435 else 1445) else (if i < 603 then 1462 else 1448)) else (if i < 606 then (if i < 605 then 1466 else 1457) else (if i < 607 then 1454 else 1468)))))

private def parentEdgeValue_b19 (i : ℕ) : ℕ :=
  (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then 1446 else 1455) else (if i < 611 then 1452 else 1458)) else (if i < 614 then (if i < 613 then 1473 else 1474) else (if i < 615 then 1491 else 1483))) else (if i < 620 then (if i < 618 then (if i < 617 then 1480 else 1493) else (if i < 619 then 1472 else 1481)) else (if i < 622 then (if i < 621 then 1478 else 1484) else (if i < 623 then 1502 else 1511)))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then 1515 else 1776) else (if i < 627 then 1543 else 1524)) else (if i < 630 then (if i < 629 then 1541 else 1542) else (if i < 631 then 1527 else 1767))) else (if i < 636 then (if i < 634 then (if i < 633 then 1525 else 1532) else (if i < 635 then 1533 else 1528)) else (if i < 638 then (if i < 637 then 1537 else 1547) else (if i < 639 then 1564 else 1550)))))

private def parentEdgeValue_b20 (i : ℕ) : ℕ :=
  (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then 1568 else 1559) else (if i < 643 then 1556 else 1570)) else (if i < 646 then (if i < 645 then 1548 else 1557) else (if i < 647 then 1554 else 1560))) else (if i < 652 then (if i < 650 then (if i < 649 then 1575 else 1576) else (if i < 651 then 1593 else 1585)) else (if i < 654 then (if i < 653 then 1591 else 1595) else (if i < 655 then 1574 else 1583)))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then 1580 else 1586) else (if i < 659 then 1774 else 1761)) else (if i < 662 then (if i < 661 then 1619 else 1759) else (if i < 663 then 1617 else 1754))) else (if i < 668 then (if i < 666 then (if i < 665 then 1752 else 1602) else (if i < 667 then 1611 else 1610)) else (if i < 670 then (if i < 669 then 1604 else 1615) else (if i < 671 then 1620 else 1640)))))

private def parentEdgeValue_b21 (i : ℕ) : ℕ :=
  (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then 1626 else 1644) else (if i < 675 then 1635 else 1632)) else (if i < 678 then (if i < 677 then 1646 else 1624) else (if i < 679 then 1633 else 1630))) else (if i < 684 then (if i < 682 then (if i < 681 then 1636 else 1651) else (if i < 683 then 1652 else 1670)) else (if i < 686 then (if i < 685 then 1661 else 1658) else (if i < 687 then 1672 else 1650)))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then 1659 else 1656) else (if i < 691 then 1662 else 1777)) else (if i < 694 then (if i < 693 then 1768 else 1676) else (if i < 695 then 1766 else 1694))) else (if i < 700 then (if i < 698 then (if i < 697 then 1679 else 1760) else (if i < 699 then 1677 else 1684)) else (if i < 702 then (if i < 701 then 1685 else 1680) else (if i < 703 then 1689 else 1699)))))

private def parentEdgeValue_b22 (i : ℕ) : ℕ :=
  (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then 1716 else 1702) else (if i < 707 then 1720 else 1711)) else (if i < 710 then (if i < 709 then 1708 else 1722) else (if i < 711 then 1700 else 1709))) else (if i < 716 then (if i < 714 then (if i < 713 then 1706 else 1712) else (if i < 715 then 1727 else 1728)) else (if i < 718 then (if i < 717 then 1745 else 1737) else (if i < 719 then 1734 else 1747)))) else (if i < 728 then (if i < 724 then (if i < 722 then (if i < 721 then 1726 else 1735) else (if i < 723 then 1732 else 1738)) else (if i < 726 then (if i < 725 then 1755 else 1765) else (if i < 727 then 1772 else 2029))) else (if i < 732 then (if i < 730 then (if i < 729 then 1797 else 1779) else (if i < 731 then 2030 else 1787)) else (if i < 734 then (if i < 733 then 2022 else 2020) else (if i < 735 then 1780 else 1789)))))

private def parentEdgeValue_b23 (i : ℕ) : ℕ :=
  (if i < 752 then (if i < 744 then (if i < 740 then (if i < 738 then (if i < 737 then 1788 else 1785) else (if i < 739 then 1793 else 1801)) else (if i < 742 then (if i < 741 then 1818 else 1827) else (if i < 743 then 1822 else 1813))) else (if i < 748 then (if i < 746 then (if i < 745 then 1810 else 1824) else (if i < 747 then 1802 else 1811)) else (if i < 750 then (if i < 749 then 1807 else 1814) else (if i < 751 then 1829 else 1830)))) else (if i < 760 then (if i < 756 then (if i < 754 then (if i < 753 then 1847 else 1852) else (if i < 755 then 1845 else 1849)) else (if i < 758 then (if i < 757 then 1828 else 1838) else (if i < 759 then 1834 else 1843))) else (if i < 764 then (if i < 762 then (if i < 761 then 2028 else 2015) else (if i < 763 then 1873 else 2013)) else (if i < 766 then (if i < 765 then 1871 else 1857) else (if i < 767 then 1865 else 1855)))))

private def parentEdgeValue_b24 (i : ℕ) : ℕ :=
  (if i < 784 then (if i < 776 then (if i < 772 then (if i < 770 then (if i < 769 then 1862 else 1863) else (if i < 771 then 1859 else 1867)) else (if i < 774 then (if i < 773 then 1874 else 1879) else (if i < 775 then 1880 else 1897))) else (if i < 780 then (if i < 778 then (if i < 777 then 1902 else 1895) else (if i < 779 then 1899 else 1878)) else (if i < 782 then (if i < 781 then 1887 else 1884) else (if i < 783 then 1890 else 1920)))) else (if i < 792 then (if i < 788 then (if i < 786 then (if i < 785 then 1929 else 1924) else (if i < 787 then 1915 else 1912)) else (if i < 790 then (if i < 789 then 1926 else 1922) else (if i < 791 then 1913 else 1911))) else (if i < 796 then (if i < 794 then (if i < 793 then 1916 else 2031) else (if i < 795 then 1949 else 1930)) else (if i < 798 then (if i < 797 then 1947 else 1948) else (if i < 799 then 1933 else 2014)))))

private def parentEdgeValue_b25 (i : ℕ) : ℕ :=
  (if i < 816 then (if i < 808 then (if i < 804 then (if i < 802 then (if i < 801 then 1931 else 1938) else (if i < 803 then 1939 else 1934)) else (if i < 806 then (if i < 805 then 1943 else 1953) else (if i < 807 then 1970 else 1956))) else (if i < 812 then (if i < 810 then (if i < 809 then 1974 else 1965) else (if i < 811 then 1962 else 1976)) else (if i < 814 then (if i < 813 then 1954 else 1963) else (if i < 815 then 1960 else 1966)))) else (if i < 824 then (if i < 820 then (if i < 818 then (if i < 817 then 1981 else 1982) else (if i < 819 then 1999 else 1991)) else (if i < 822 then (if i < 821 then 1997 else 2001) else (if i < 823 then 1980 else 1989))) else (if i < 828 then (if i < 826 then (if i < 825 then 1986 else 1992) else (if i < 827 then 2010 else 2019)) else (if i < 830 then (if i < 829 then 2023 else 2283) else (if i < 831 then 2051 else 2032)))))

private def parentEdgeValue_b26 (i : ℕ) : ℕ :=
  (if i < 848 then (if i < 840 then (if i < 836 then (if i < 834 then (if i < 833 then 2284 else 2050) else (if i < 835 then 2276 else 2274)) else (if i < 838 then (if i < 837 then 2034 else 2043) else (if i < 839 then 2042 else 2039))) else (if i < 844 then (if i < 842 then (if i < 841 then 2047 else 2055) else (if i < 843 then 2072 else 2081)) else (if i < 846 then (if i < 845 then 2076 else 2067) else (if i < 847 then 2064 else 2078)))) else (if i < 856 then (if i < 852 then (if i < 850 then (if i < 849 then 2056 else 2065) else (if i < 851 then 2061 else 2068)) else (if i < 854 then (if i < 853 then 2083 else 2084) else (if i < 855 then 2101 else 2106))) else (if i < 860 then (if i < 858 then (if i < 857 then 2099 else 2103) else (if i < 859 then 2082 else 2092)) else (if i < 862 then (if i < 861 then 2088 else 2097) else (if i < 863 then 2282 else 2269)))))

private def parentEdgeValue_b27 (i : ℕ) : ℕ :=
  (if i < 880 then (if i < 872 then (if i < 868 then (if i < 866 then (if i < 865 then 2127 else 2267) else (if i < 867 then 2125 else 2111)) else (if i < 870 then (if i < 869 then 2119 else 2109) else (if i < 871 then 2116 else 2117))) else (if i < 876 then (if i < 874 then (if i < 873 then 2113 else 2121) else (if i < 875 then 2128 else 2133)) else (if i < 878 then (if i < 877 then 2134 else 2151) else (if i < 879 then 2156 else 2149)))) else (if i < 888 then (if i < 884 then (if i < 882 then (if i < 881 then 2153 else 2132) else (if i < 883 then 2141 else 2138)) else (if i < 886 then (if i < 885 then 2144 else 2174) else (if i < 887 then 2183 else 2178))) else (if i < 892 then (if i < 890 then (if i < 889 then 2169 else 2166) else (if i < 891 then 2180 else 2176)) else (if i < 894 then (if i < 893 then 2167 else 2165) else (if i < 895 then 2170 else 2285)))))

private def parentEdgeValue_b28 (i : ℕ) : ℕ :=
  (if i < 912 then (if i < 904 then (if i < 900 then (if i < 898 then (if i < 897 then 2203 else 2184) else (if i < 899 then 2201 else 2202)) else (if i < 902 then (if i < 901 then 2187 else 2268) else (if i < 903 then 2185 else 2192))) else (if i < 908 then (if i < 906 then (if i < 905 then 2193 else 2188) else (if i < 907 then 2197 else 2207)) else (if i < 910 then (if i < 909 then 2224 else 2210) else (if i < 911 then 2228 else 2219)))) else (if i < 920 then (if i < 916 then (if i < 914 then (if i < 913 then 2216 else 2230) else (if i < 915 then 2208 else 2217)) else (if i < 918 then (if i < 917 then 2214 else 2220) else (if i < 919 then 2235 else 2236))) else (if i < 924 then (if i < 922 then (if i < 921 then 2253 else 2245) else (if i < 923 then 2251 else 2255)) else (if i < 926 then (if i < 925 then 2234 else 2243) else (if i < 927 then 2240 else 2246)))))

private def parentEdgeValue_b29 (i : ℕ) : ℕ :=
  (if i < 944 then (if i < 936 then (if i < 932 then (if i < 930 then (if i < 929 then 2264 else 2273) else (if i < 931 then 2277 else 2537)) else (if i < 934 then (if i < 933 then 2516 else 2286) else (if i < 935 then 2514 else 2304))) else (if i < 940 then (if i < 938 then (if i < 937 then 2289 else 2529) else (if i < 939 then 2287 else 2294)) else (if i < 942 then (if i < 941 then 2295 else 2290) else (if i < 943 then 2299 else 2309)))) else (if i < 952 then (if i < 948 then (if i < 946 then (if i < 945 then 2326 else 2312) else (if i < 947 then 2330 else 2321)) else (if i < 950 then (if i < 949 then 2318 else 2332) else (if i < 951 then 2310 else 2319))) else (if i < 956 then (if i < 954 then (if i < 953 then 2316 else 2322) else (if i < 955 then 2337 else 2338)) else (if i < 958 then (if i < 957 then 2355 else 2347) else (if i < 959 then 2344 else 2357)))))

private def parentEdgeValue_b30 (i : ℕ) : ℕ :=
  (if i < 976 then (if i < 968 then (if i < 964 then (if i < 962 then (if i < 961 then 2336 else 2345) else (if i < 963 then 2342 else 2348)) else (if i < 966 then (if i < 965 then 2536 else 2523) else (if i < 967 then 2362 else 2521))) else (if i < 972 then (if i < 970 then (if i < 969 then 2380 else 2365) else (if i < 971 then 2515 else 2363)) else (if i < 974 then (if i < 973 then 2370 else 2371) else (if i < 975 then 2366 else 2375)))) else (if i < 984 then (if i < 980 then (if i < 978 then (if i < 977 then 2385 else 2402) else (if i < 979 then 2388 else 2406)) else (if i < 982 then (if i < 981 then 2397 else 2394) else (if i < 983 then 2408 else 2386))) else (if i < 988 then (if i < 986 then (if i < 985 then 2395 else 2392) else (if i < 987 then 2398 else 2413)) else (if i < 990 then (if i < 989 then 2414 else 2431) else (if i < 991 then 2423 else 2420)))))

private def parentEdgeValue_b31 (i : ℕ) : ℕ :=
  (if i < 1008 then (if i < 1000 then (if i < 996 then (if i < 994 then (if i < 993 then 2433 else 2412) else (if i < 995 then 2421 else 2418)) else (if i < 998 then (if i < 997 then 2424 else 2539) else (if i < 999 then 2457 else 2438))) else (if i < 1004 then (if i < 1002 then (if i < 1001 then 2455 else 2456) else (if i < 1003 then 2441 else 2522)) else (if i < 1006 then (if i < 1005 then 2439 else 2446) else (if i < 1007 then 2447 else 2442)))) else (if i < 1016 then (if i < 1012 then (if i < 1010 then (if i < 1009 then 2451 else 2461) else (if i < 1011 then 2478 else 2464)) else (if i < 1014 then (if i < 1013 then 2482 else 2473) else (if i < 1015 then 2470 else 2484))) else (if i < 1020 then (if i < 1018 then (if i < 1017 then 2462 else 2471) else (if i < 1019 then 2468 else 2474)) else (if i < 1022 then (if i < 1021 then 2489 else 2490) else (if i < 1023 then 2507 else 2499)))))

private def parentEdgeValue_b32 (i : ℕ) : ℕ :=
  (if i < 1040 then (if i < 1032 then (if i < 1028 then (if i < 1026 then (if i < 1025 then 2505 else 2509) else (if i < 1027 then 2488 else 2497)) else (if i < 1030 then (if i < 1029 then 2494 else 2500) else (if i < 1031 then 2520 else 2527))) else (if i < 1036 then (if i < 1034 then (if i < 1033 then 2534 else 2620) else (if i < 1035 then 2621 else 2626)) else (if i < 1038 then (if i < 1037 then 2625 else 2630) else (if i < 1039 then 2629 else 2541)))) else (if i < 1048 then (if i < 1044 then (if i < 1042 then (if i < 1041 then 2542 else 2544) else (if i < 1043 then 2552 else 2558)) else (if i < 1046 then (if i < 1045 then 2562 else 2570) else (if i < 1047 then 2573 else 2580))) else (if i < 1052 then (if i < 1050 then (if i < 1049 then 2588 else 2592) else (if i < 1051 then 2600 else 2606)) else (if i < 1054 then (if i < 1053 then 2612 else 2618) else (if i < 1055 then 2619 else 2622)))))

private def parentEdgeValue_b33 (i : ℕ) : ℕ :=
  (if i < 1057 then 2623 else 2631)

private def parentEdgeValue_n0_0 (i : ℕ) : ℕ := if i < 32 then parentEdgeValue_b0 i else parentEdgeValue_b1 i

private def parentEdgeValue_n0_1 (i : ℕ) : ℕ := if i < 96 then parentEdgeValue_b2 i else parentEdgeValue_b3 i

private def parentEdgeValue_n0_2 (i : ℕ) : ℕ := if i < 160 then parentEdgeValue_b4 i else parentEdgeValue_b5 i

private def parentEdgeValue_n0_3 (i : ℕ) : ℕ := if i < 224 then parentEdgeValue_b6 i else parentEdgeValue_b7 i

private def parentEdgeValue_n0_4 (i : ℕ) : ℕ := if i < 288 then parentEdgeValue_b8 i else parentEdgeValue_b9 i

private def parentEdgeValue_n0_5 (i : ℕ) : ℕ := if i < 352 then parentEdgeValue_b10 i else parentEdgeValue_b11 i

private def parentEdgeValue_n0_6 (i : ℕ) : ℕ := if i < 416 then parentEdgeValue_b12 i else parentEdgeValue_b13 i

private def parentEdgeValue_n0_7 (i : ℕ) : ℕ := if i < 480 then parentEdgeValue_b14 i else parentEdgeValue_b15 i

private def parentEdgeValue_n0_8 (i : ℕ) : ℕ := if i < 544 then parentEdgeValue_b16 i else parentEdgeValue_b17 i

private def parentEdgeValue_n0_9 (i : ℕ) : ℕ := if i < 608 then parentEdgeValue_b18 i else parentEdgeValue_b19 i

private def parentEdgeValue_n0_10 (i : ℕ) : ℕ := if i < 672 then parentEdgeValue_b20 i else parentEdgeValue_b21 i

private def parentEdgeValue_n0_11 (i : ℕ) : ℕ := if i < 736 then parentEdgeValue_b22 i else parentEdgeValue_b23 i

private def parentEdgeValue_n0_12 (i : ℕ) : ℕ := if i < 800 then parentEdgeValue_b24 i else parentEdgeValue_b25 i

private def parentEdgeValue_n0_13 (i : ℕ) : ℕ := if i < 864 then parentEdgeValue_b26 i else parentEdgeValue_b27 i

private def parentEdgeValue_n0_14 (i : ℕ) : ℕ := if i < 928 then parentEdgeValue_b28 i else parentEdgeValue_b29 i

private def parentEdgeValue_n0_15 (i : ℕ) : ℕ := if i < 992 then parentEdgeValue_b30 i else parentEdgeValue_b31 i

private def parentEdgeValue_n0_16 (i : ℕ) : ℕ := if i < 1056 then parentEdgeValue_b32 i else parentEdgeValue_b33 i

private def parentEdgeValue_n1_0 (i : ℕ) : ℕ := if i < 64 then parentEdgeValue_n0_0 i else parentEdgeValue_n0_1 i

private def parentEdgeValue_n1_1 (i : ℕ) : ℕ := if i < 192 then parentEdgeValue_n0_2 i else parentEdgeValue_n0_3 i

private def parentEdgeValue_n1_2 (i : ℕ) : ℕ := if i < 320 then parentEdgeValue_n0_4 i else parentEdgeValue_n0_5 i

private def parentEdgeValue_n1_3 (i : ℕ) : ℕ := if i < 448 then parentEdgeValue_n0_6 i else parentEdgeValue_n0_7 i

private def parentEdgeValue_n1_4 (i : ℕ) : ℕ := if i < 576 then parentEdgeValue_n0_8 i else parentEdgeValue_n0_9 i

private def parentEdgeValue_n1_5 (i : ℕ) : ℕ := if i < 704 then parentEdgeValue_n0_10 i else parentEdgeValue_n0_11 i

private def parentEdgeValue_n1_6 (i : ℕ) : ℕ := if i < 832 then parentEdgeValue_n0_12 i else parentEdgeValue_n0_13 i

private def parentEdgeValue_n1_7 (i : ℕ) : ℕ := if i < 960 then parentEdgeValue_n0_14 i else parentEdgeValue_n0_15 i

private def parentEdgeValue_n2_0 (i : ℕ) : ℕ := if i < 128 then parentEdgeValue_n1_0 i else parentEdgeValue_n1_1 i

private def parentEdgeValue_n2_1 (i : ℕ) : ℕ := if i < 384 then parentEdgeValue_n1_2 i else parentEdgeValue_n1_3 i

private def parentEdgeValue_n2_2 (i : ℕ) : ℕ := if i < 640 then parentEdgeValue_n1_4 i else parentEdgeValue_n1_5 i

private def parentEdgeValue_n2_3 (i : ℕ) : ℕ := if i < 896 then parentEdgeValue_n1_6 i else parentEdgeValue_n1_7 i

private def parentEdgeValue_n3_0 (i : ℕ) : ℕ := if i < 256 then parentEdgeValue_n2_0 i else parentEdgeValue_n2_1 i

private def parentEdgeValue_n3_1 (i : ℕ) : ℕ := if i < 768 then parentEdgeValue_n2_2 i else parentEdgeValue_n2_3 i

private def parentEdgeValue_n4_0 (i : ℕ) : ℕ := if i < 512 then parentEdgeValue_n3_0 i else parentEdgeValue_n3_1 i

private def parentEdgeValue_n5_0 (i : ℕ) : ℕ := if i < 1024 then parentEdgeValue_n4_0 i else parentEdgeValue_n0_16 i

def parentEdgeValue (i : ℕ) : ℕ := parentEdgeValue_n5_0 i

end PlanarHom.ColoringMacroFaces.FanFramed
