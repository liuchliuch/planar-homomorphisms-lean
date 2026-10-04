import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.TestFramed
private def hostValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 1 else 5) else (if i < 3 then 5 else 10)) else (if i < 6 then (if i < 5 then 10 else 8) else (if i < 7 then 8 else 1))) else (if i < 12 then (if i < 10 then (if i < 9 then 1 else 13) else (if i < 11 then 5 else 13)) else (if i < 14 then (if i < 13 then 10 else 13) else (if i < 15 then 8 else 13)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 11 else 7) else (if i < 19 then 7 else 12)) else (if i < 22 then (if i < 21 then 12 else 9) else (if i < 23 then 9 else 11))) else (if i < 28 then (if i < 26 then (if i < 25 then 11 else 14) else (if i < 27 then 7 else 14)) else (if i < 30 then (if i < 29 then 12 else 14) else (if i < 31 then 9 else 14)))))

private def hostValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 4 else 6) else (if i < 35 then 6 else 7)) else (if i < 38 then (if i < 37 then 7 else 5) else (if i < 39 then 5 else 4))) else (if i < 44 then (if i < 42 then (if i < 41 then 4 else 15) else (if i < 43 then 6 else 15)) else (if i < 46 then (if i < 45 then 7 else 15) else (if i < 47 then 5 else 15)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 22 else 16) else (if i < 51 then 16 else 7)) else (if i < 54 then (if i < 53 then 7 else 17) else (if i < 55 then 17 else 22))) else (if i < 60 then (if i < 58 then (if i < 57 then 22 else 24) else (if i < 59 then 16 else 24)) else (if i < 62 then (if i < 61 then 7 else 24) else (if i < 63 then 17 else 24)))))

private def hostValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 8 else 20) else (if i < 67 then 20 else 23)) else (if i < 70 then (if i < 69 then 23 else 19) else (if i < 71 then 19 else 8))) else (if i < 76 then (if i < 74 then (if i < 73 then 8 else 25) else (if i < 75 then 20 else 25)) else (if i < 78 then (if i < 77 then 23 else 25) else (if i < 79 then 19 else 25)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 10 else 16) else (if i < 83 then 10 else 20)) else (if i < 86 then (if i < 85 then 22 else 18) else (if i < 87 then 18 else 17))) else (if i < 92 then (if i < 90 then (if i < 89 then 18 else 20) else (if i < 91 then 17 else 21)) else (if i < 94 then (if i < 93 then 20 else 21) else (if i < 95 then 21 else 23)))))

private def hostValue_b3 (i : ℕ) : ℕ :=
  (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 19 else 11) else (if i < 99 then 17 else 11)) else (if i < 102 then (if i < 101 then 32 else 26) else (if i < 103 then 26 else 9))) else (if i < 108 then (if i < 106 then (if i < 105 then 9 else 27) else (if i < 107 then 27 else 32)) else (if i < 110 then (if i < 109 then 32 else 34) else (if i < 111 then 26 else 34)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 9 else 34) else (if i < 115 then 27 else 34)) else (if i < 118 then (if i < 117 then 6 else 30) else (if i < 119 then 30 else 33))) else (if i < 124 then (if i < 122 then (if i < 121 then 33 else 29) else (if i < 123 then 29 else 6)) else (if i < 126 then (if i < 125 then 6 else 35) else (if i < 127 then 30 else 35)))))

private def hostValue_b4 (i : ℕ) : ℕ :=
  (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 33 else 35) else (if i < 131 then 29 else 35)) else (if i < 134 then (if i < 133 then 12 else 26) else (if i < 135 then 12 else 30))) else (if i < 140 then (if i < 138 then (if i < 137 then 32 else 28) else (if i < 139 then 28 else 27)) else (if i < 142 then (if i < 141 then 28 else 30) else (if i < 143 then 27 else 31)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 30 else 31) else (if i < 147 then 31 else 33)) else (if i < 150 then (if i < 149 then 29 else 3) else (if i < 151 then 27 else 3))) else (if i < 156 then (if i < 154 then (if i < 153 then 0 else 38) else (if i < 155 then 38 else 43)) else (if i < 158 then (if i < 157 then 43 else 41) else (if i < 159 then 41 else 0)))))

private def hostValue_b5 (i : ℕ) : ℕ :=
  (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 0 else 46) else (if i < 163 then 38 else 46)) else (if i < 166 then (if i < 165 then 43 else 46) else (if i < 167 then 41 else 46))) else (if i < 172 then (if i < 170 then (if i < 169 then 44 else 40) else (if i < 171 then 40 else 45)) else (if i < 174 then (if i < 173 then 45 else 42) else (if i < 175 then 42 else 44)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 44 else 47) else (if i < 179 then 40 else 47)) else (if i < 182 then (if i < 181 then 45 else 47) else (if i < 183 then 42 else 47))) else (if i < 188 then (if i < 186 then (if i < 185 then 37 else 39) else (if i < 187 then 39 else 40)) else (if i < 190 then (if i < 189 then 40 else 38) else (if i < 191 then 38 else 37)))))

private def hostValue_b6 (i : ℕ) : ℕ :=
  (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 37 else 48) else (if i < 195 then 39 else 48)) else (if i < 198 then (if i < 197 then 40 else 48) else (if i < 199 then 38 else 48))) else (if i < 204 then (if i < 202 then (if i < 201 then 55 else 49) else (if i < 203 then 49 else 40)) else (if i < 206 then (if i < 205 then 40 else 50) else (if i < 207 then 50 else 55)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 55 else 57) else (if i < 211 then 49 else 57)) else (if i < 214 then (if i < 213 then 40 else 57) else (if i < 215 then 50 else 57))) else (if i < 220 then (if i < 218 then (if i < 217 then 41 else 53) else (if i < 219 then 53 else 56)) else (if i < 222 then (if i < 221 then 56 else 52) else (if i < 223 then 52 else 41)))))

private def hostValue_b7 (i : ℕ) : ℕ :=
  (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 41 else 58) else (if i < 227 then 53 else 58)) else (if i < 230 then (if i < 229 then 56 else 58) else (if i < 231 then 52 else 58))) else (if i < 236 then (if i < 234 then (if i < 233 then 43 else 49) else (if i < 235 then 43 else 53)) else (if i < 238 then (if i < 237 then 55 else 51) else (if i < 239 then 51 else 50)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 51 else 53) else (if i < 243 then 50 else 54)) else (if i < 246 then (if i < 245 then 53 else 54) else (if i < 247 then 54 else 56))) else (if i < 252 then (if i < 250 then (if i < 249 then 52 else 44) else (if i < 251 then 50 else 44)) else (if i < 254 then (if i < 253 then 65 else 59) else (if i < 255 then 59 else 42)))))

private def hostValue_b8 (i : ℕ) : ℕ :=
  (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 42 else 60) else (if i < 259 then 60 else 65)) else (if i < 262 then (if i < 261 then 65 else 67) else (if i < 263 then 59 else 67))) else (if i < 268 then (if i < 266 then (if i < 265 then 42 else 67) else (if i < 267 then 60 else 67)) else (if i < 270 then (if i < 269 then 39 else 63) else (if i < 271 then 63 else 66)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 66 else 62) else (if i < 275 then 62 else 39)) else (if i < 278 then (if i < 277 then 39 else 68) else (if i < 279 then 63 else 68))) else (if i < 284 then (if i < 282 then (if i < 281 then 66 else 68) else (if i < 283 then 62 else 68)) else (if i < 286 then (if i < 285 then 45 else 59) else (if i < 287 then 45 else 63)))))

private def hostValue_b9 (i : ℕ) : ℕ :=
  (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 65 else 61) else (if i < 291 then 61 else 60)) else (if i < 294 then (if i < 293 then 61 else 63) else (if i < 295 then 60 else 64))) else (if i < 300 then (if i < 298 then (if i < 297 then 63 else 64) else (if i < 299 then 64 else 66)) else (if i < 302 then (if i < 301 then 62 else 36) else (if i < 303 then 60 else 36)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 2 else 71) else (if i < 307 then 71 else 76)) else (if i < 310 then (if i < 309 then 76 else 74) else (if i < 311 then 74 else 2))) else (if i < 316 then (if i < 314 then (if i < 313 then 2 else 79) else (if i < 315 then 71 else 79)) else (if i < 318 then (if i < 317 then 76 else 79) else (if i < 319 then 74 else 79)))))

private def hostValue_b10 (i : ℕ) : ℕ :=
  (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 77 else 73) else (if i < 323 then 73 else 78)) else (if i < 326 then (if i < 325 then 78 else 75) else (if i < 327 then 75 else 77))) else (if i < 332 then (if i < 330 then (if i < 329 then 77 else 80) else (if i < 331 then 73 else 80)) else (if i < 334 then (if i < 333 then 78 else 80) else (if i < 335 then 75 else 80)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 70 else 72) else (if i < 339 then 72 else 73)) else (if i < 342 then (if i < 341 then 73 else 71) else (if i < 343 then 71 else 70))) else (if i < 348 then (if i < 346 then (if i < 345 then 70 else 81) else (if i < 347 then 72 else 81)) else (if i < 350 then (if i < 349 then 73 else 81) else (if i < 351 then 71 else 81)))))

private def hostValue_b11 (i : ℕ) : ℕ :=
  (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 88 else 82) else (if i < 355 then 82 else 73)) else (if i < 358 then (if i < 357 then 73 else 83) else (if i < 359 then 83 else 88))) else (if i < 364 then (if i < 362 then (if i < 361 then 88 else 90) else (if i < 363 then 82 else 90)) else (if i < 366 then (if i < 365 then 73 else 90) else (if i < 367 then 83 else 90)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 74 else 86) else (if i < 371 then 86 else 89)) else (if i < 374 then (if i < 373 then 89 else 85) else (if i < 375 then 85 else 74))) else (if i < 380 then (if i < 378 then (if i < 377 then 74 else 91) else (if i < 379 then 86 else 91)) else (if i < 382 then (if i < 381 then 89 else 91) else (if i < 383 then 85 else 91)))))

private def hostValue_b12 (i : ℕ) : ℕ :=
  (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 76 else 82) else (if i < 387 then 76 else 86)) else (if i < 390 then (if i < 389 then 88 else 84) else (if i < 391 then 84 else 83))) else (if i < 396 then (if i < 394 then (if i < 393 then 84 else 86) else (if i < 395 then 83 else 87)) else (if i < 398 then (if i < 397 then 86 else 87) else (if i < 399 then 87 else 89)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 85 else 77) else (if i < 403 then 83 else 77)) else (if i < 406 then (if i < 405 then 98 else 92) else (if i < 407 then 92 else 75))) else (if i < 412 then (if i < 410 then (if i < 409 then 75 else 93) else (if i < 411 then 93 else 98)) else (if i < 414 then (if i < 413 then 98 else 100) else (if i < 415 then 92 else 100)))))

private def hostValue_b13 (i : ℕ) : ℕ :=
  (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 75 else 100) else (if i < 419 then 93 else 100)) else (if i < 422 then (if i < 421 then 72 else 96) else (if i < 423 then 96 else 99))) else (if i < 428 then (if i < 426 then (if i < 425 then 99 else 95) else (if i < 427 then 95 else 72)) else (if i < 430 then (if i < 429 then 72 else 101) else (if i < 431 then 96 else 101)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 99 else 101) else (if i < 435 then 95 else 101)) else (if i < 438 then (if i < 437 then 78 else 92) else (if i < 439 then 78 else 96))) else (if i < 444 then (if i < 442 then (if i < 441 then 98 else 94) else (if i < 443 then 94 else 93)) else (if i < 446 then (if i < 445 then 94 else 96) else (if i < 447 then 93 else 97)))))

private def hostValue_b14 (i : ℕ) : ℕ :=
  (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 96 else 97) else (if i < 451 then 97 else 99)) else (if i < 454 then (if i < 453 then 95 else 69) else (if i < 455 then 93 else 69))) else (if i < 460 then (if i < 458 then (if i < 457 then 6 else 42) else (if i < 459 then 42 else 41)) else (if i < 462 then (if i < 461 then 41 else 4) else (if i < 463 then 4 else 102)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 6 else 102) else (if i < 467 then 42 else 102)) else (if i < 470 then (if i < 469 then 41 else 102) else (if i < 471 then 39 else 75))) else (if i < 476 then (if i < 474 then (if i < 473 then 75 else 74) else (if i < 475 then 74 else 37)) else (if i < 478 then (if i < 477 then 37 else 103) else (if i < 479 then 39 else 103)))))

private def hostValue_b15 (i : ℕ) : ℕ :=
  (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 75 else 103) else (if i < 483 then 74 else 103)) else (if i < 486 then (if i < 485 then 72 else 9) else (if i < 487 then 9 else 8))) else (if i < 492 then (if i < 490 then (if i < 489 then 8 else 70) else (if i < 491 then 70 else 104)) else (if i < 494 then (if i < 493 then 72 else 104) else (if i < 495 then 9 else 104)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 8 else 104) else (if i < 499 then 3 else 36)) else (if i < 502 then (if i < 501 then 36 else 69) else (if i < 503 then 69 else 3))) else (if i < 508 then (if i < 506 then (if i < 505 then 3 else 6) else (if i < 507 then 69 else 75)) else (if i < 510 then (if i < 509 then 74 else 105) else (if i < 511 then 106 else 37)))))

private def hostValue_b16 (i : ℕ) : ℕ :=
  (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 37 else 111) else (if i < 515 then 74 else 111)) else (if i < 518 then (if i < 517 then 105 else 111) else (if i < 519 then 106 else 111))) else (if i < 524 then (if i < 522 then (if i < 521 then 41 else 107) else (if i < 523 then 108 else 4)) else (if i < 526 then (if i < 525 then 4 else 112) else (if i < 527 then 41 else 112)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 107 else 112) else (if i < 531 then 108 else 112)) else (if i < 534 then (if i < 533 then 8 else 109) else (if i < 535 then 110 else 70))) else (if i < 540 then (if i < 538 then (if i < 537 then 70 else 113) else (if i < 539 then 8 else 113)) else (if i < 542 then (if i < 541 then 109 else 113) else (if i < 543 then 110 else 113)))))

private def hostValue_b17 (i : ℕ) : ℕ :=
  (if i < 557 then (if i < 550 then (if i < 547 then (if i < 545 then 114 else (if i < 546 then 105 else 105)) else (if i < 548 then 106 else (if i < 549 then 106 else 0))) else (if i < 553 then (if i < 551 then 0 else (if i < 552 then 107 else 107)) else (if i < 555 then (if i < 554 then 108 else 108) else (if i < 556 then 1 else 1)))) else (if i < 563 then (if i < 560 then (if i < 558 then 109 else (if i < 559 then 109 else 110)) else (if i < 561 then 110 else (if i < 562 then 2 else 2))) else (if i < 566 then (if i < 564 then 115 else (if i < 565 then 115 else 116)) else (if i < 568 then (if i < 567 then 116 else 117) else (if i < 569 then 117 else 114)))))

private def hostValue_n0_0 (i : ℕ) : ℕ := if i < 32 then hostValue_b0 i else hostValue_b1 i

private def hostValue_n0_1 (i : ℕ) : ℕ := if i < 96 then hostValue_b2 i else hostValue_b3 i

private def hostValue_n0_2 (i : ℕ) : ℕ := if i < 160 then hostValue_b4 i else hostValue_b5 i

private def hostValue_n0_3 (i : ℕ) : ℕ := if i < 224 then hostValue_b6 i else hostValue_b7 i

private def hostValue_n0_4 (i : ℕ) : ℕ := if i < 288 then hostValue_b8 i else hostValue_b9 i

private def hostValue_n0_5 (i : ℕ) : ℕ := if i < 352 then hostValue_b10 i else hostValue_b11 i

private def hostValue_n0_6 (i : ℕ) : ℕ := if i < 416 then hostValue_b12 i else hostValue_b13 i

private def hostValue_n0_7 (i : ℕ) : ℕ := if i < 480 then hostValue_b14 i else hostValue_b15 i

private def hostValue_n0_8 (i : ℕ) : ℕ := if i < 544 then hostValue_b16 i else hostValue_b17 i

private def hostValue_n1_0 (i : ℕ) : ℕ := if i < 64 then hostValue_n0_0 i else hostValue_n0_1 i

private def hostValue_n1_1 (i : ℕ) : ℕ := if i < 192 then hostValue_n0_2 i else hostValue_n0_3 i

private def hostValue_n1_2 (i : ℕ) : ℕ := if i < 320 then hostValue_n0_4 i else hostValue_n0_5 i

private def hostValue_n1_3 (i : ℕ) : ℕ := if i < 448 then hostValue_n0_6 i else hostValue_n0_7 i

private def hostValue_n2_0 (i : ℕ) : ℕ := if i < 128 then hostValue_n1_0 i else hostValue_n1_1 i

private def hostValue_n2_1 (i : ℕ) : ℕ := if i < 384 then hostValue_n1_2 i else hostValue_n1_3 i

private def hostValue_n3_0 (i : ℕ) : ℕ := if i < 256 then hostValue_n2_0 i else hostValue_n2_1 i

private def hostValue_n4_0 (i : ℕ) : ℕ := if i < 512 then hostValue_n3_0 i else hostValue_n0_8 i

def hostValue (i : ℕ) : ℕ := hostValue_n4_0 i

end PlanarHom.ColoringMacroFaces.TestFramed
