import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.WireFramed
private def parentEdgeValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 1318) else (if i < 3 then 76 else 3)) else (if i < 6 then (if i < 5 then 584 else 511) else (if i < 7 then 838 else 251))) else (if i < 12 then (if i < 10 then (if i < 9 then 19 else 1) else (if i < 11 then 252 else 9)) else (if i < 14 then (if i < 13 then 244 else 242) else (if i < 15 then 2 else 11)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 10 else 7) else (if i < 19 then 15 else 23)) else (if i < 22 then (if i < 21 then 40 else 49) else (if i < 23 then 44 else 35))) else (if i < 28 then (if i < 26 then (if i < 25 then 32 else 46) else (if i < 27 then 24 else 33)) else (if i < 30 then (if i < 29 then 29 else 36) else (if i < 31 then 51 else 52)))))

private def parentEdgeValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 69 else 74) else (if i < 35 then 67 else 71)) else (if i < 38 then (if i < 37 then 50 else 60) else (if i < 39 then 56 else 65))) else (if i < 44 then (if i < 42 then (if i < 41 then 250 else 237) else (if i < 43 then 95 else 235)) else (if i < 46 then (if i < 45 then 93 else 79) else (if i < 47 then 87 else 77)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 84 else 85) else (if i < 51 then 81 else 89)) else (if i < 54 then (if i < 53 then 96 else 101) else (if i < 55 then 102 else 119))) else (if i < 60 then (if i < 58 then (if i < 57 then 124 else 117) else (if i < 59 then 121 else 100)) else (if i < 62 then (if i < 61 then 109 else 106) else (if i < 63 then 112 else 142)))))

private def parentEdgeValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 151 else 146) else (if i < 67 then 137 else 134)) else (if i < 70 then (if i < 69 then 148 else 144) else (if i < 71 then 135 else 133))) else (if i < 76 then (if i < 74 then (if i < 73 then 138 else 253) else (if i < 75 then 171 else 152)) else (if i < 78 then (if i < 77 then 169 else 170) else (if i < 79 then 155 else 236)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 153 else 160) else (if i < 83 then 161 else 156)) else (if i < 86 then (if i < 85 then 165 else 175) else (if i < 87 then 192 else 178))) else (if i < 92 then (if i < 90 then (if i < 89 then 196 else 187) else (if i < 91 then 184 else 198)) else (if i < 94 then (if i < 93 then 176 else 185) else (if i < 95 then 182 else 188)))))

private def parentEdgeValue_b3 (i : ℕ) : ℕ :=
  (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 203 else 204) else (if i < 99 then 221 else 213)) else (if i < 102 then (if i < 101 then 219 else 223) else (if i < 103 then 202 else 211))) else (if i < 108 then (if i < 106 then (if i < 105 then 208 else 214) else (if i < 107 then 232 else 241)) else (if i < 110 then (if i < 109 then 245 else 506) else (if i < 111 then 484 else 254)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 482 else 272) else (if i < 115 then 257 else 497)) else (if i < 118 then (if i < 117 then 255 else 262) else (if i < 119 then 263 else 258))) else (if i < 124 then (if i < 122 then (if i < 121 then 267 else 277) else (if i < 123 then 294 else 280)) else (if i < 126 then (if i < 125 then 298 else 289) else (if i < 127 then 286 else 300)))))

private def parentEdgeValue_b4 (i : ℕ) : ℕ :=
  (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 278 else 287) else (if i < 131 then 284 else 290)) else (if i < 134 then (if i < 133 then 305 else 306) else (if i < 135 then 323 else 315))) else (if i < 140 then (if i < 138 then (if i < 137 then 312 else 325) else (if i < 139 then 304 else 313)) else (if i < 142 then (if i < 141 then 310 else 316) else (if i < 143 then 405 else 349)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 330 else 347) else (if i < 147 then 348 else 333)) else (if i < 150 then (if i < 149 then 483 else 331) else (if i < 151 then 338 else 339))) else (if i < 156 then (if i < 154 then (if i < 153 then 334 else 343) else (if i < 155 then 353 else 370)) else (if i < 158 then (if i < 157 then 356 else 374) else (if i < 159 then 365 else 362)))))

private def parentEdgeValue_b5 (i : ℕ) : ℕ :=
  (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 376 else 354) else (if i < 163 then 363 else 360)) else (if i < 166 then (if i < 165 then 366 else 381) else (if i < 167 then 382 else 399))) else (if i < 172 then (if i < 170 then (if i < 169 then 391 else 397) else (if i < 171 then 401 else 380)) else (if i < 174 then (if i < 173 then 389 else 386) else (if i < 175 then 392 else 507)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 498 else 406) else (if i < 179 then 496 else 424)) else (if i < 182 then (if i < 181 then 409 else 490) else (if i < 183 then 407 else 414))) else (if i < 188 then (if i < 186 then (if i < 185 then 415 else 410) else (if i < 187 then 419 else 429)) else (if i < 190 then (if i < 189 then 446 else 432) else (if i < 191 then 450 else 441)))))

private def parentEdgeValue_b6 (i : ℕ) : ℕ :=
  (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 438 else 452) else (if i < 195 then 430 else 439)) else (if i < 198 then (if i < 197 then 436 else 442) else (if i < 199 then 457 else 458))) else (if i < 204 then (if i < 202 then (if i < 201 then 475 else 467) else (if i < 203 then 464 else 477)) else (if i < 206 then (if i < 205 then 456 else 465) else (if i < 207 then 462 else 468)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 488 else 495) else (if i < 211 then 502 else 759)) else (if i < 214 then (if i < 213 then 738 else 509) else (if i < 215 then 760 else 525))) else (if i < 220 then (if i < 218 then (if i < 217 then 752 else 750) else (if i < 219 then 510 else 519)) else (if i < 222 then (if i < 221 then 518 else 515) else (if i < 223 then 523 else 529)))))

private def parentEdgeValue_b7 (i : ℕ) : ℕ :=
  (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 548 else 534) else (if i < 227 then 552 else 543)) else (if i < 230 then (if i < 229 then 540 else 554) else (if i < 231 then 532 else 541))) else (if i < 236 then (if i < 234 then (if i < 233 then 538 else 544) else (if i < 235 then 559 else 583)) else (if i < 238 then (if i < 237 then 577 else 582) else (if i < 239 then 566 else 579)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 561 else 568) else (if i < 243 then 565 else 573)) else (if i < 246 then (if i < 245 then 758 else 1295) else (if i < 247 then 603 else 600))) else (if i < 252 then (if i < 250 then (if i < 249 then 601 else 587) else (if i < 251 then 595 else 585)) else (if i < 254 then (if i < 253 then 592 else 593) else (if i < 255 then 589 else 597)))))

private def parentEdgeValue_b8 (i : ℕ) : ℕ :=
  (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 604 else 609) else (if i < 259 then 610 else 627)) else (if i < 262 then (if i < 261 then 632 else 625) else (if i < 263 then 629 else 608))) else (if i < 268 then (if i < 266 then (if i < 265 then 617 else 614) else (if i < 267 then 620 else 650)) else (if i < 270 then (if i < 269 then 659 else 654) else (if i < 271 then 645 else 642)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 656 else 652) else (if i < 275 then 643 else 641)) else (if i < 278 then (if i < 277 then 646 else 761) else (if i < 279 then 679 else 660))) else (if i < 284 then (if i < 282 then (if i < 281 then 677 else 678) else (if i < 283 then 1296 else 744)) else (if i < 286 then (if i < 285 then 662 else 708) else (if i < 287 then 670 else 667)))))

private def parentEdgeValue_b9 (i : ℕ) : ℕ :=
  (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 675 else 683) else (if i < 291 then 700 else 703)) else (if i < 294 then (if i < 293 then 704 else 695) else (if i < 295 then 692 else 706))) else (if i < 300 then (if i < 298 then (if i < 297 then 684 else 693) else (if i < 299 then 689 else 696)) else (if i < 302 then (if i < 301 then 711 else 712) else (if i < 303 then 729 else 734)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 727 else 731) else (if i < 307 then 710 else 719)) else (if i < 310 then (if i < 309 then 716 else 723) else (if i < 311 then 742 else 749))) else (if i < 316 then (if i < 314 then (if i < 313 then 753 else 1013) else (if i < 315 then 781 else 762)) else (if i < 318 then (if i < 317 then 1014 else 780) else (if i < 319 then 1006 else 1004)))))

private def parentEdgeValue_b10 (i : ℕ) : ℕ :=
  (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 764 else 773) else (if i < 323 then 772 else 766)) else (if i < 326 then (if i < 325 then 777 else 785) else (if i < 327 then 802 else 788))) else (if i < 332 then (if i < 330 then (if i < 329 then 806 else 797) else (if i < 331 then 794 else 808)) else (if i < 334 then (if i < 333 then 786 else 795) else (if i < 335 then 792 else 798)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 813 else 814) else (if i < 339 then 831 else 836)) else (if i < 342 then (if i < 341 then 829 else 833) else (if i < 343 then 812 else 822))) else (if i < 348 then (if i < 346 then (if i < 345 then 818 else 827) else (if i < 347 then 1012 else 999)) else (if i < 350 then (if i < 349 then 857 else 997) else (if i < 351 then 855 else 841)))))

private def parentEdgeValue_b11 (i : ℕ) : ℕ :=
  (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 849 else 839) else (if i < 355 then 846 else 847)) else (if i < 358 then (if i < 357 then 843 else 851) else (if i < 359 then 858 else 863))) else (if i < 364 then (if i < 362 then (if i < 361 then 864 else 881) else (if i < 363 then 886 else 879)) else (if i < 366 then (if i < 365 then 883 else 862) else (if i < 367 then 871 else 868)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 874 else 904) else (if i < 371 then 913 else 908)) else (if i < 374 then (if i < 373 then 899 else 896) else (if i < 375 then 910 else 906))) else (if i < 380 then (if i < 378 then (if i < 377 then 897 else 895) else (if i < 379 then 900 else 1015)) else (if i < 382 then (if i < 381 then 933 else 914) else (if i < 383 then 931 else 932)))))

private def parentEdgeValue_b12 (i : ℕ) : ℕ :=
  (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 917 else 998) else (if i < 387 then 915 else 922)) else (if i < 390 then (if i < 389 then 923 else 918) else (if i < 391 then 927 else 937))) else (if i < 396 then (if i < 394 then (if i < 393 then 954 else 940) else (if i < 395 then 958 else 949)) else (if i < 398 then (if i < 397 then 946 else 960) else (if i < 399 then 938 else 947)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 944 else 950) else (if i < 403 then 965 else 966)) else (if i < 406 then (if i < 405 then 983 else 975) else (if i < 407 then 981 else 985))) else (if i < 412 then (if i < 410 then (if i < 409 then 964 else 973) else (if i < 411 then 970 else 976)) else (if i < 414 then (if i < 413 then 993 else 1003) else (if i < 415 then 1007 else 1268)))))

private def parentEdgeValue_b13 (i : ℕ) : ℕ :=
  (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 1246 else 1016) else (if i < 419 then 1244 else 1034)) else (if i < 422 then (if i < 421 then 1019 else 1259) else (if i < 423 then 1017 else 1024))) else (if i < 428 then (if i < 426 then (if i < 425 then 1025 else 1020) else (if i < 427 then 1029 else 1036)) else (if i < 430 then (if i < 429 then 1056 else 1042) else (if i < 431 then 1060 else 1051)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 1048 else 1062) else (if i < 435 then 1040 else 1049)) else (if i < 438 then (if i < 437 then 1046 else 1052) else (if i < 439 then 1067 else 1068))) else (if i < 444 then (if i < 442 then (if i < 441 then 1086 else 1077) else (if i < 443 then 1074 else 1088)) else (if i < 446 then (if i < 445 then 1066 else 1075) else (if i < 447 then 1072 else 1078)))))

private def parentEdgeValue_b14 (i : ℕ) : ℕ :=
  (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 1167 else 1307) else (if i < 451 then 1092 else 1108)) else (if i < 454 then (if i < 453 then 1110 else 1095) else (if i < 455 then 1245 else 1093))) else (if i < 460 then (if i < 458 then (if i < 457 then 1100 else 1101) else (if i < 459 then 1096 else 1105)) else (if i < 462 then (if i < 461 then 1115 else 1132) else (if i < 463 then 1118 else 1136)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 1127 else 1124) else (if i < 467 then 1138 else 1116)) else (if i < 470 then (if i < 469 then 1125 else 1122) else (if i < 471 then 1128 else 1143))) else (if i < 476 then (if i < 474 then (if i < 473 then 1144 else 1161) else (if i < 475 then 1153 else 1150)) else (if i < 478 then (if i < 477 then 1163 else 1142) else (if i < 479 then 1151 else 1148)))))

private def parentEdgeValue_b15 (i : ℕ) : ℕ :=
  (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 1154 else 1269) else (if i < 483 then 1187 else 1168)) else (if i < 486 then (if i < 485 then 1185 else 1186) else (if i < 487 then 1171 else 1252))) else (if i < 492 then (if i < 490 then (if i < 489 then 1169 else 1176) else (if i < 491 then 1177 else 1172)) else (if i < 494 then (if i < 493 then 1181 else 1191) else (if i < 495 then 1208 else 1194)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 1212 else 1203) else (if i < 499 then 1200 else 1214)) else (if i < 502 then (if i < 501 then 1192 else 1201) else (if i < 503 then 1198 else 1204))) else (if i < 508 then (if i < 506 then (if i < 505 then 1219 else 1220) else (if i < 507 then 1237 else 1229)) else (if i < 510 then (if i < 509 then 1235 else 1239) else (if i < 511 then 1218 else 1227)))))

private def parentEdgeValue_b16 (i : ℕ) : ℕ :=
  (if i < 523 then (if i < 517 then (if i < 514 then (if i < 513 then 1224 else 1230) else (if i < 515 then 1250 else (if i < 516 then 1254 else 1264))) else (if i < 520 then (if i < 518 then 1314 else (if i < 519 then 1315 else 1321)) else (if i < 521 then 1319 else (if i < 522 then 1271 else 1272)))) else (if i < 528 then (if i < 525 then (if i < 524 then 1274 else 1282) else (if i < 526 then 1288 else (if i < 527 then 1294 else 1297))) else (if i < 531 then (if i < 529 then 1306 else (if i < 530 then 1310 else 1313)) else (if i < 532 then 1316 else (if i < 533 then 1317 else 1322)))))

private def parentEdgeValue_n0_0 (i : ℕ) : ℕ := if i < 32 then parentEdgeValue_b0 i else parentEdgeValue_b1 i

private def parentEdgeValue_n0_1 (i : ℕ) : ℕ := if i < 96 then parentEdgeValue_b2 i else parentEdgeValue_b3 i

private def parentEdgeValue_n0_2 (i : ℕ) : ℕ := if i < 160 then parentEdgeValue_b4 i else parentEdgeValue_b5 i

private def parentEdgeValue_n0_3 (i : ℕ) : ℕ := if i < 224 then parentEdgeValue_b6 i else parentEdgeValue_b7 i

private def parentEdgeValue_n0_4 (i : ℕ) : ℕ := if i < 288 then parentEdgeValue_b8 i else parentEdgeValue_b9 i

private def parentEdgeValue_n0_5 (i : ℕ) : ℕ := if i < 352 then parentEdgeValue_b10 i else parentEdgeValue_b11 i

private def parentEdgeValue_n0_6 (i : ℕ) : ℕ := if i < 416 then parentEdgeValue_b12 i else parentEdgeValue_b13 i

private def parentEdgeValue_n0_7 (i : ℕ) : ℕ := if i < 480 then parentEdgeValue_b14 i else parentEdgeValue_b15 i

private def parentEdgeValue_n1_0 (i : ℕ) : ℕ := if i < 64 then parentEdgeValue_n0_0 i else parentEdgeValue_n0_1 i

private def parentEdgeValue_n1_1 (i : ℕ) : ℕ := if i < 192 then parentEdgeValue_n0_2 i else parentEdgeValue_n0_3 i

private def parentEdgeValue_n1_2 (i : ℕ) : ℕ := if i < 320 then parentEdgeValue_n0_4 i else parentEdgeValue_n0_5 i

private def parentEdgeValue_n1_3 (i : ℕ) : ℕ := if i < 448 then parentEdgeValue_n0_6 i else parentEdgeValue_n0_7 i

private def parentEdgeValue_n2_0 (i : ℕ) : ℕ := if i < 128 then parentEdgeValue_n1_0 i else parentEdgeValue_n1_1 i

private def parentEdgeValue_n2_1 (i : ℕ) : ℕ := if i < 384 then parentEdgeValue_n1_2 i else parentEdgeValue_n1_3 i

private def parentEdgeValue_n3_0 (i : ℕ) : ℕ := if i < 256 then parentEdgeValue_n2_0 i else parentEdgeValue_n2_1 i

private def parentEdgeValue_n4_0 (i : ℕ) : ℕ := if i < 512 then parentEdgeValue_n3_0 i else parentEdgeValue_b16 i

def parentEdgeValue (i : ℕ) : ℕ := parentEdgeValue_n4_0 i

end PlanarHom.ColoringMacroFaces.WireFramed
