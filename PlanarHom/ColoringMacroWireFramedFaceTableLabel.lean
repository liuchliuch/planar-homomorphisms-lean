import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.WireFramed
private def labelValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 1) else (if i < 3 then 2 else 3)) else (if i < 6 then (if i < 5 then 4 else 5) else (if i < 7 then 6 else 7))) else (if i < 12 then (if i < 10 then (if i < 9 then 6 else 0) else (if i < 11 then 0 else 2)) else (if i < 14 then (if i < 13 then 2 else 4) else (if i < 15 then 4 else 6)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 8 else 9) else (if i < 19 then 10 else 11)) else (if i < 22 then (if i < 21 then 12 else 13) else (if i < 23 then 14 else 15))) else (if i < 28 then (if i < 26 then (if i < 25 then 14 else 8) else (if i < 27 then 8 else 10)) else (if i < 30 then (if i < 29 then 10 else 12) else (if i < 31 then 12 else 14)))))

private def labelValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 16 else 17) else (if i < 35 then 18 else 11)) else (if i < 38 then (if i < 37 then 19 else 3) else (if i < 39 then 20 else 1))) else (if i < 44 then (if i < 42 then (if i < 41 then 20 else 16) else (if i < 43 then 16 else 18)) else (if i < 46 then (if i < 45 then 18 else 19) else (if i < 47 then 19 else 20)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 21 else 22) else (if i < 51 then 23 else 3)) else (if i < 54 then (if i < 53 then 24 else 9) else (if i < 55 then 25 else 26))) else (if i < 60 then (if i < 58 then (if i < 57 then 25 else 21) else (if i < 59 then 21 else 23)) else (if i < 62 then (if i < 61 then 23 else 24) else (if i < 63 then 24 else 25)))))

private def labelValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 27 else 5) else (if i < 67 then 28 else 29)) else (if i < 70 then (if i < 69 then 30 else 31) else (if i < 71 then 32 else 15))) else (if i < 76 then (if i < 74 then (if i < 73 then 32 else 27) else (if i < 75 then 27 else 28)) else (if i < 78 then (if i < 77 then 28 else 30) else (if i < 79 then 30 else 32)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 22 else 3) else (if i < 83 then 5 else 22)) else (if i < 86 then (if i < 85 then 22 else 26) else (if i < 87 then 33 else 26))) else (if i < 92 then (if i < 90 then (if i < 89 then 22 else 33) else (if i < 91 then 33 else 31)) else (if i < 94 then (if i < 93 then 29 else 33) else (if i < 95 then 29 else 31)))))

private def labelValue_b3 (i : ℕ) : ℕ :=
  (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 15 else 31) else (if i < 99 then 31 else 9)) else (if i < 102 then (if i < 101 then 34 else 35) else (if i < 103 then 13 else 36))) else (if i < 108 then (if i < 106 then (if i < 105 then 37 else 38) else (if i < 107 then 39 else 40)) else (if i < 110 then (if i < 109 then 35 else 40) else (if i < 111 then 36 else 35)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 38 else 36) else (if i < 115 then 40 else 38)) else (if i < 118 then (if i < 117 then 11 else 41) else (if i < 119 then 42 else 43))) else (if i < 124 then (if i < 122 then (if i < 121 then 44 else 45) else (if i < 123 then 46 else 47)) else (if i < 126 then (if i < 125 then 41 else 47) else (if i < 127 then 43 else 41)))))

private def labelValue_b4 (i : ℕ) : ℕ :=
  (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 45 else 43) else (if i < 131 then 47 else 45)) else (if i < 134 then (if i < 133 then 13 else 34) else (if i < 135 then 34 else 11))) else (if i < 140 then (if i < 138 then (if i < 137 then 39 else 34) else (if i < 139 then 39 else 48)) else (if i < 142 then (if i < 141 then 48 else 34) else (if i < 143 then 44 else 48)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 48 else 42) else (if i < 147 then 44 else 42)) else (if i < 150 then (if i < 149 then 44 else 46) else (if i < 151 then 37 else 44))) else (if i < 156 then (if i < 154 then (if i < 153 then 49 else 50) else (if i < 155 then 51 else 52)) else (if i < 158 then (if i < 157 then 53 else 54) else (if i < 159 then 55 else 56)))))

private def labelValue_b5 (i : ℕ) : ℕ :=
  (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 55 else 49) else (if i < 163 then 49 else 51)) else (if i < 166 then (if i < 165 then 51 else 53) else (if i < 167 then 53 else 55))) else (if i < 172 then (if i < 170 then (if i < 169 then 57 else 58) else (if i < 171 then 59 else 60)) else (if i < 174 then (if i < 173 then 61 else 62) else (if i < 175 then 63 else 64)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 63 else 57) else (if i < 179 then 57 else 59)) else (if i < 182 then (if i < 181 then 59 else 61) else (if i < 183 then 61 else 63))) else (if i < 188 then (if i < 186 then (if i < 185 then 65 else 66) else (if i < 187 then 67 else 60)) else (if i < 190 then (if i < 189 then 68 else 52) else (if i < 191 then 69 else 50)))))

private def labelValue_b6 (i : ℕ) : ℕ :=
  (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 69 else 65) else (if i < 195 then 65 else 67)) else (if i < 198 then (if i < 197 then 67 else 68) else (if i < 199 then 68 else 69))) else (if i < 204 then (if i < 202 then (if i < 201 then 70 else 71) else (if i < 203 then 72 else 52)) else (if i < 206 then (if i < 205 then 73 else 58) else (if i < 207 then 74 else 75)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 74 else 70) else (if i < 211 then 70 else 72)) else (if i < 214 then (if i < 213 then 72 else 73) else (if i < 215 then 73 else 74))) else (if i < 220 then (if i < 218 then (if i < 217 then 76 else 54) else (if i < 219 then 77 else 78)) else (if i < 222 then (if i < 221 then 79 else 80) else (if i < 223 then 81 else 64)))))

private def labelValue_b7 (i : ℕ) : ℕ :=
  (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 81 else 76) else (if i < 227 then 76 else 77)) else (if i < 230 then (if i < 229 then 77 else 79) else (if i < 231 then 79 else 81))) else (if i < 236 then (if i < 234 then (if i < 233 then 71 else 52) else (if i < 235 then 54 else 71)) else (if i < 238 then (if i < 237 then 71 else 75) else (if i < 239 then 82 else 75)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 71 else 82) else (if i < 243 then 82 else 80)) else (if i < 246 then (if i < 245 then 78 else 82) else (if i < 247 then 78 else 80))) else (if i < 252 then (if i < 250 then (if i < 249 then 64 else 80) else (if i < 251 then 80 else 58)) else (if i < 254 then (if i < 253 then 83 else 84) else (if i < 255 then 62 else 85)))))

private def labelValue_b8 (i : ℕ) : ℕ :=
  (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 86 else 87) else (if i < 259 then 88 else 89)) else (if i < 262 then (if i < 261 then 84 else 89) else (if i < 263 then 85 else 84))) else (if i < 268 then (if i < 266 then (if i < 265 then 87 else 85) else (if i < 267 then 89 else 87)) else (if i < 270 then (if i < 269 then 60 else 90) else (if i < 271 then 91 else 92)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 93 else 94) else (if i < 275 then 95 else 96)) else (if i < 278 then (if i < 277 then 90 else 96) else (if i < 279 then 92 else 90))) else (if i < 284 then (if i < 282 then (if i < 281 then 94 else 92) else (if i < 283 then 96 else 94)) else (if i < 286 then (if i < 285 then 62 else 83) else (if i < 287 then 83 else 60)))))

private def labelValue_b9 (i : ℕ) : ℕ :=
  (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 88 else 83) else (if i < 291 then 88 else 97)) else (if i < 294 then (if i < 293 then 97 else 83) else (if i < 295 then 93 else 97))) else (if i < 300 then (if i < 298 then (if i < 297 then 97 else 91) else (if i < 299 then 93 else 91)) else (if i < 302 then (if i < 301 then 93 else 95) else (if i < 303 then 86 else 93)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 98 else 99) else (if i < 307 then 100 else 101)) else (if i < 310 then (if i < 309 then 102 else 103) else (if i < 311 then 104 else 105))) else (if i < 316 then (if i < 314 then (if i < 313 then 104 else 98) else (if i < 315 then 98 else 100)) else (if i < 318 then (if i < 317 then 100 else 102) else (if i < 319 then 102 else 104)))))

private def labelValue_b10 (i : ℕ) : ℕ :=
  (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 106 else 107) else (if i < 323 then 108 else 109)) else (if i < 326 then (if i < 325 then 110 else 111) else (if i < 327 then 112 else 113))) else (if i < 332 then (if i < 330 then (if i < 329 then 112 else 106) else (if i < 331 then 106 else 108)) else (if i < 334 then (if i < 333 then 108 else 110) else (if i < 335 then 110 else 112)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 114 else 115) else (if i < 339 then 116 else 109)) else (if i < 342 then (if i < 341 then 117 else 101) else (if i < 343 then 118 else 99))) else (if i < 348 then (if i < 346 then (if i < 345 then 118 else 114) else (if i < 347 then 114 else 116)) else (if i < 350 then (if i < 349 then 116 else 117) else (if i < 351 then 117 else 118)))))

private def labelValue_b11 (i : ℕ) : ℕ :=
  (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 119 else 120) else (if i < 355 then 121 else 101)) else (if i < 358 then (if i < 357 then 122 else 107) else (if i < 359 then 123 else 124))) else (if i < 364 then (if i < 362 then (if i < 361 then 123 else 119) else (if i < 363 then 119 else 121)) else (if i < 366 then (if i < 365 then 121 else 122) else (if i < 367 then 122 else 123)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 125 else 103) else (if i < 371 then 126 else 127)) else (if i < 374 then (if i < 373 then 128 else 129) else (if i < 375 then 130 else 113))) else (if i < 380 then (if i < 378 then (if i < 377 then 130 else 125) else (if i < 379 then 125 else 126)) else (if i < 382 then (if i < 381 then 126 else 128) else (if i < 383 then 128 else 130)))))

private def labelValue_b12 (i : ℕ) : ℕ :=
  (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 120 else 101) else (if i < 387 then 103 else 120)) else (if i < 390 then (if i < 389 then 120 else 124) else (if i < 391 then 131 else 124))) else (if i < 396 then (if i < 394 then (if i < 393 then 120 else 131) else (if i < 395 then 131 else 129)) else (if i < 398 then (if i < 397 then 127 else 131) else (if i < 399 then 127 else 129)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 113 else 129) else (if i < 403 then 129 else 107)) else (if i < 406 then (if i < 405 then 132 else 133) else (if i < 407 then 111 else 134))) else (if i < 412 then (if i < 410 then (if i < 409 then 135 else 136) else (if i < 411 then 137 else 138)) else (if i < 414 then (if i < 413 then 133 else 138) else (if i < 415 then 134 else 133)))))

private def labelValue_b13 (i : ℕ) : ℕ :=
  (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 136 else 134) else (if i < 419 then 138 else 136)) else (if i < 422 then (if i < 421 then 109 else 139) else (if i < 423 then 140 else 141))) else (if i < 428 then (if i < 426 then (if i < 425 then 142 else 143) else (if i < 427 then 37 else 144)) else (if i < 430 then (if i < 429 then 139 else 144) else (if i < 431 then 141 else 139)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 143 else 141) else (if i < 435 then 144 else 143)) else (if i < 438 then (if i < 437 then 111 else 132) else (if i < 439 then 132 else 109))) else (if i < 444 then (if i < 442 then (if i < 441 then 137 else 132) else (if i < 443 then 137 else 145)) else (if i < 446 then (if i < 445 then 145 else 132) else (if i < 447 then 142 else 145)))))

private def labelValue_b14 (i : ℕ) : ℕ :=
  (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 145 else 140) else (if i < 451 then 142 else 140)) else (if i < 454 then (if i < 453 then 142 else 37) else (if i < 455 then 135 else 142))) else (if i < 460 then (if i < 458 then (if i < 457 then 86 else 146) else (if i < 459 then 64 else 147)) else (if i < 462 then (if i < 461 then 148 else 149) else (if i < 463 then 17 else 149)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 146 else 17) else (if i < 467 then 147 else 146)) else (if i < 470 then (if i < 469 then 149 else 147) else (if i < 471 then 95 else 150))) else (if i < 476 then (if i < 474 then (if i < 473 then 113 else 151) else (if i < 475 then 152 else 153)) else (if i < 478 then (if i < 477 then 66 else 153) else (if i < 479 then 150 else 66)))))

private def labelValue_b15 (i : ℕ) : ℕ :=
  (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 151 else 150) else (if i < 483 then 153 else 151)) else (if i < 486 then (if i < 485 then 37 else 154) else (if i < 487 then 15 else 155))) else (if i < 492 then (if i < 490 then (if i < 489 then 156 else 157) else (if i < 491 then 115 else 157)) else (if i < 494 then (if i < 493 then 154 else 115) else (if i < 495 then 155 else 154)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 157 else 155) else (if i < 499 then 158 else 86)) else (if i < 502 then (if i < 501 then 158 else 95) else (if i < 503 then 158 else 37))) else (if i < 508 then (if i < 506 then (if i < 505 then 86 else 46) else (if i < 507 then 135 else 95)) else (if i < 510 then (if i < 509 then 159 else 99) else (if i < 511 then 160 else 161)))))

private def labelValue_b16 (i : ℕ) : ℕ :=
  (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 162 else 163) else (if i < 515 then 164 else 1)) else (if i < 518 then (if i < 517 then 164 else 159) else (if i < 519 then 159 else 160))) else (if i < 524 then (if i < 522 then (if i < 521 then 160 else 162) else (if i < 523 then 162 else 164)) else (if i < 526 then (if i < 525 then 165 else 166) else (if i < 527 then 167 else 168)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 169 else 170) else (if i < 531 then 171 else 172)) else (if i < 534 then (if i < 533 then 171 else 165) else (if i < 535 then 165 else 167))) else (if i < 540 then (if i < 538 then (if i < 537 then 167 else 169) else (if i < 539 then 169 else 171)) else (if i < 542 then (if i < 541 then 173 else 174) else (if i < 543 then 175 else 168)))))

private def labelValue_b17 (i : ℕ) : ℕ :=
  (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then 176 else 161) else (if i < 547 then 177 else 99)) else (if i < 550 then (if i < 549 then 177 else 173) else (if i < 551 then 173 else 175))) else (if i < 556 then (if i < 554 then (if i < 553 then 175 else 176) else (if i < 555 then 176 else 177)) else (if i < 558 then (if i < 557 then 178 else 179) else (if i < 559 then 180 else 161)))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then 181 else 166) else (if i < 563 then 182 else 183)) else (if i < 566 then (if i < 565 then 182 else 178) else (if i < 567 then 178 else 180))) else (if i < 572 then (if i < 570 then (if i < 569 then 180 else 181) else (if i < 571 then 181 else 182)) else (if i < 574 then (if i < 573 then 184 else 163) else (if i < 575 then 185 else 186)))))

private def labelValue_b18 (i : ℕ) : ℕ :=
  (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then 187 else 188) else (if i < 579 then 189 else 172)) else (if i < 582 then (if i < 581 then 189 else 184) else (if i < 583 then 184 else 185))) else (if i < 588 then (if i < 586 then (if i < 585 then 185 else 187) else (if i < 587 then 187 else 189)) else (if i < 590 then (if i < 589 then 179 else 161) else (if i < 591 then 163 else 179)))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then 179 else 183) else (if i < 595 then 190 else 183)) else (if i < 598 then (if i < 597 then 179 else 190) else (if i < 599 then 190 else 188))) else (if i < 604 then (if i < 602 then (if i < 601 then 186 else 190) else (if i < 603 then 186 else 188)) else (if i < 606 then (if i < 605 then 172 else 188) else (if i < 607 then 188 else 166)))))

private def labelValue_b19 (i : ℕ) : ℕ :=
  (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then 191 else 192) else (if i < 611 then 170 else 193)) else (if i < 614 then (if i < 613 then 194 else 195) else (if i < 615 then 196 else 197))) else (if i < 620 then (if i < 618 then (if i < 617 then 192 else 197) else (if i < 619 then 193 else 192)) else (if i < 622 then (if i < 621 then 195 else 193) else (if i < 623 then 197 else 195)))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then 168 else 198) else (if i < 627 then 199 else 200)) else (if i < 630 then (if i < 629 then 201 else 202) else (if i < 631 then 203 else 204))) else (if i < 636 then (if i < 634 then (if i < 633 then 198 else 204) else (if i < 635 then 200 else 198)) else (if i < 638 then (if i < 637 then 202 else 200) else (if i < 639 then 204 else 202)))))

private def labelValue_b20 (i : ℕ) : ℕ :=
  (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then 170 else 191) else (if i < 643 then 191 else 168)) else (if i < 646 then (if i < 645 then 196 else 191) else (if i < 647 then 196 else 205))) else (if i < 652 then (if i < 650 then (if i < 649 then 205 else 191) else (if i < 651 then 201 else 205)) else (if i < 654 then (if i < 653 then 205 else 199) else (if i < 655 then 201 else 199)))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then 201 else 203) else (if i < 659 then 194 else 201)) else (if i < 662 then (if i < 661 then 206 else 207) else (if i < 663 then 208 else 209))) else (if i < 668 then (if i < 666 then (if i < 665 then 210 else 211) else (if i < 667 then 212 else 99)) else (if i < 670 then (if i < 669 then 212 else 206) else (if i < 671 then 206 else 208)))))

private def labelValue_b21 (i : ℕ) : ℕ :=
  (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then 208 else 210) else (if i < 675 then 210 else 212)) else (if i < 678 then (if i < 677 then 213 else 214) else (if i < 679 then 215 else 216))) else (if i < 684 then (if i < 682 then (if i < 681 then 217 else 218) else (if i < 683 then 219 else 220)) else (if i < 686 then (if i < 685 then 219 else 213) else (if i < 687 then 213 else 215)))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then 215 else 217) else (if i < 691 then 217 else 219)) else (if i < 694 then (if i < 693 then 221 else 222) else (if i < 695 then 223 else 216))) else (if i < 700 then (if i < 698 then (if i < 697 then 224 else 209) else (if i < 699 then 225 else 207)) else (if i < 702 then (if i < 701 then 225 else 221) else (if i < 703 then 221 else 223)))))

private def labelValue_b22 (i : ℕ) : ℕ :=
  (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then 223 else 224) else (if i < 707 then 224 else 225)) else (if i < 710 then (if i < 709 then 226 else 227) else (if i < 711 then 228 else 209))) else (if i < 716 then (if i < 714 then (if i < 713 then 229 else 214) else (if i < 715 then 230 else 231)) else (if i < 718 then (if i < 717 then 230 else 226) else (if i < 719 then 226 else 228)))) else (if i < 728 then (if i < 724 then (if i < 722 then (if i < 721 then 228 else 229) else (if i < 723 then 229 else 230)) else (if i < 726 then (if i < 725 then 232 else 211) else (if i < 727 then 233 else 234))) else (if i < 732 then (if i < 730 then (if i < 729 then 235 else 236) else (if i < 731 then 237 else 220)) else (if i < 734 then (if i < 733 then 237 else 232) else (if i < 735 then 232 else 233)))))

private def labelValue_b23 (i : ℕ) : ℕ :=
  (if i < 752 then (if i < 744 then (if i < 740 then (if i < 738 then (if i < 737 then 233 else 235) else (if i < 739 then 235 else 237)) else (if i < 742 then (if i < 741 then 227 else 209) else (if i < 743 then 211 else 227))) else (if i < 748 then (if i < 746 then (if i < 745 then 227 else 231) else (if i < 747 then 238 else 231)) else (if i < 750 then (if i < 749 then 227 else 238) else (if i < 751 then 238 else 236)))) else (if i < 760 then (if i < 756 then (if i < 754 then (if i < 753 then 234 else 238) else (if i < 755 then 234 else 236)) else (if i < 758 then (if i < 757 then 220 else 236) else (if i < 759 then 236 else 214))) else (if i < 764 then (if i < 762 then (if i < 761 then 239 else 240) else (if i < 763 then 218 else 241)) else (if i < 766 then (if i < 765 then 242 else 243) else (if i < 767 then 244 else 245)))))

private def labelValue_b24 (i : ℕ) : ℕ :=
  (if i < 784 then (if i < 776 then (if i < 772 then (if i < 770 then (if i < 769 then 240 else 245) else (if i < 771 then 241 else 240)) else (if i < 774 then (if i < 773 then 243 else 241) else (if i < 775 then 245 else 243))) else (if i < 780 then (if i < 778 then (if i < 777 then 216 else 246) else (if i < 779 then 247 else 248)) else (if i < 782 then (if i < 781 then 249 else 250) else (if i < 783 then 251 else 252)))) else (if i < 792 then (if i < 788 then (if i < 786 then (if i < 785 then 246 else 252) else (if i < 787 then 248 else 246)) else (if i < 790 then (if i < 789 then 250 else 248) else (if i < 791 then 252 else 250))) else (if i < 796 then (if i < 794 then (if i < 793 then 218 else 239) else (if i < 795 then 239 else 216)) else (if i < 798 then (if i < 797 then 244 else 239) else (if i < 799 then 244 else 253)))))

private def labelValue_b25 (i : ℕ) : ℕ :=
  (if i < 816 then (if i < 808 then (if i < 804 then (if i < 802 then (if i < 801 then 253 else 239) else (if i < 803 then 249 else 253)) else (if i < 806 then (if i < 805 then 253 else 247) else (if i < 807 then 249 else 247))) else (if i < 812 then (if i < 810 then (if i < 809 then 249 else 251) else (if i < 811 then 242 else 249)) else (if i < 814 then (if i < 813 then 254 else 56) else (if i < 815 then 255 else 256)))) else (if i < 824 then (if i < 820 then (if i < 818 then (if i < 817 then 257 else 258) else (if i < 819 then 259 else 50)) else (if i < 822 then (if i < 821 then 259 else 254) else (if i < 823 then 254 else 255))) else (if i < 828 then (if i < 826 then (if i < 825 then 255 else 257) else (if i < 827 then 257 else 259)) else (if i < 830 then (if i < 829 then 260 else 261) else (if i < 831 then 262 else 263)))))

private def labelValue_b26 (i : ℕ) : ℕ :=
  (if i < 848 then (if i < 840 then (if i < 836 then (if i < 834 then (if i < 833 then 264 else 265) else (if i < 835 then 266 else 267)) else (if i < 838 then (if i < 837 then 266 else 260) else (if i < 839 then 260 else 262))) else (if i < 844 then (if i < 842 then (if i < 841 then 262 else 264) else (if i < 843 then 264 else 266)) else (if i < 846 then (if i < 845 then 268 else 269) else (if i < 847 then 270 else 263)))) else (if i < 856 then (if i < 852 then (if i < 850 then (if i < 849 then 271 else 256) else (if i < 851 then 272 else 56)) else (if i < 854 then (if i < 853 then 272 else 268) else (if i < 855 then 268 else 270))) else (if i < 860 then (if i < 858 then (if i < 857 then 270 else 271) else (if i < 859 then 271 else 272)) else (if i < 862 then (if i < 861 then 273 else 274) else (if i < 863 then 275 else 256)))))

private def labelValue_b27 (i : ℕ) : ℕ :=
  (if i < 880 then (if i < 872 then (if i < 868 then (if i < 866 then (if i < 865 then 276 else 261) else (if i < 867 then 277 else 278)) else (if i < 870 then (if i < 869 then 277 else 273) else (if i < 871 then 273 else 275))) else (if i < 876 then (if i < 874 then (if i < 873 then 275 else 276) else (if i < 875 then 276 else 277)) else (if i < 878 then (if i < 877 then 279 else 258) else (if i < 879 then 280 else 281)))) else (if i < 888 then (if i < 884 then (if i < 882 then (if i < 881 then 282 else 283) else (if i < 883 then 284 else 267)) else (if i < 886 then (if i < 885 then 284 else 279) else (if i < 887 then 279 else 280))) else (if i < 892 then (if i < 890 then (if i < 889 then 280 else 282) else (if i < 891 then 282 else 284)) else (if i < 894 then (if i < 893 then 274 else 256) else (if i < 895 then 258 else 274)))))

private def labelValue_b28 (i : ℕ) : ℕ :=
  (if i < 912 then (if i < 904 then (if i < 900 then (if i < 898 then (if i < 897 then 274 else 278) else (if i < 899 then 285 else 278)) else (if i < 902 then (if i < 901 then 274 else 285) else (if i < 903 then 285 else 283))) else (if i < 908 then (if i < 906 then (if i < 905 then 281 else 285) else (if i < 907 then 281 else 283)) else (if i < 910 then (if i < 909 then 267 else 283) else (if i < 911 then 283 else 261)))) else (if i < 920 then (if i < 916 then (if i < 914 then (if i < 913 then 286 else 287) else (if i < 915 then 265 else 288)) else (if i < 918 then (if i < 917 then 289 else 290) else (if i < 919 then 291 else 292))) else (if i < 924 then (if i < 922 then (if i < 921 then 287 else 292) else (if i < 923 then 288 else 287)) else (if i < 926 then (if i < 925 then 290 else 288) else (if i < 927 then 292 else 290)))))

private def labelValue_b29 (i : ℕ) : ℕ :=
  (if i < 944 then (if i < 936 then (if i < 932 then (if i < 930 then (if i < 929 then 263 else 293) else (if i < 931 then 294 else 295)) else (if i < 934 then (if i < 933 then 296 else 297) else (if i < 935 then 194 else 298))) else (if i < 940 then (if i < 938 then (if i < 937 then 293 else 298) else (if i < 939 then 295 else 293)) else (if i < 942 then (if i < 941 then 297 else 295) else (if i < 943 then 298 else 297)))) else (if i < 952 then (if i < 948 then (if i < 946 then (if i < 945 then 265 else 286) else (if i < 947 then 286 else 263)) else (if i < 950 then (if i < 949 then 291 else 286) else (if i < 951 then 291 else 299))) else (if i < 956 then (if i < 954 then (if i < 953 then 299 else 286) else (if i < 955 then 296 else 299)) else (if i < 958 then (if i < 957 then 299 else 294) else (if i < 959 then 296 else 294)))))

private def labelValue_b30 (i : ℕ) : ℕ :=
  (if i < 976 then (if i < 968 then (if i < 964 then (if i < 962 then (if i < 961 then 296 else 194) else (if i < 963 then 289 else 296)) else (if i < 966 then (if i < 965 then 242 else 300) else (if i < 967 then 220 else 301))) else (if i < 972 then (if i < 970 then (if i < 969 then 99 else 302) else (if i < 971 then 174 else 302)) else (if i < 974 then (if i < 973 then 300 else 174) else (if i < 975 then 301 else 300)))) else (if i < 984 then (if i < 980 then (if i < 978 then (if i < 977 then 302 else 301) else (if i < 979 then 251 else 303)) else (if i < 982 then (if i < 981 then 267 else 304) else (if i < 983 then 305 else 306))) else (if i < 988 then (if i < 986 then (if i < 985 then 222 else 306) else (if i < 987 then 303 else 222)) else (if i < 990 then (if i < 989 then 304 else 303) else (if i < 991 then 306 else 304)))))

private def labelValue_b31 (i : ℕ) : ℕ :=
  (if i < 1008 then (if i < 1000 then (if i < 996 then (if i < 994 then (if i < 993 then 194 else 307) else (if i < 995 then 172 else 308)) else (if i < 998 then (if i < 997 then 309 else 310) else (if i < 999 then 269 else 310))) else (if i < 1004 then (if i < 1002 then (if i < 1001 then 307 else 269) else (if i < 1003 then 308 else 307)) else (if i < 1006 then (if i < 1005 then 310 else 308) else (if i < 1007 then 311 else 242)))) else (if i < 1016 then (if i < 1012 then (if i < 1010 then (if i < 1009 then 311 else 251) else (if i < 1011 then 311 else 194)) else (if i < 1014 then (if i < 1013 then 242 else 203) else (if i < 1015 then 289 else 251))) else (if i < 1020 then (if i < 1018 then (if i < 1017 then 312 else 313) else (if i < 1019 then 314 else 315)) else (if i < 1022 then (if i < 1021 then 316 else 317) else (if i < 1023 then 318 else 319)))))

private def labelValue_b32 (i : ℕ) : ℕ :=
  (if i < 1040 then (if i < 1032 then (if i < 1028 then (if i < 1026 then (if i < 1025 then 318 else 312) else (if i < 1027 then 312 else 314)) else (if i < 1030 then (if i < 1029 then 314 else 316) else (if i < 1031 then 316 else 318))) else (if i < 1036 then (if i < 1034 then (if i < 1033 then 320 else 321) else (if i < 1035 then 322 else 323)) else (if i < 1038 then (if i < 1037 then 324 else 325) else (if i < 1039 then 326 else 327)))) else (if i < 1048 then (if i < 1044 then (if i < 1042 then (if i < 1041 then 326 else 320) else (if i < 1043 then 320 else 322)) else (if i < 1046 then (if i < 1045 then 322 else 324) else (if i < 1047 then 324 else 326))) else (if i < 1052 then (if i < 1050 then (if i < 1049 then 328 else 329) else (if i < 1051 then 330 else 323)) else (if i < 1054 then (if i < 1053 then 331 else 315) else (if i < 1055 then 332 else 313)))))

private def labelValue_b33 (i : ℕ) : ℕ :=
  (if i < 1072 then (if i < 1064 then (if i < 1060 then (if i < 1058 then (if i < 1057 then 332 else 328) else (if i < 1059 then 328 else 330)) else (if i < 1062 then (if i < 1061 then 330 else 331) else (if i < 1063 then 331 else 332))) else (if i < 1068 then (if i < 1066 then (if i < 1065 then 333 else 334) else (if i < 1067 then 335 else 315)) else (if i < 1070 then (if i < 1069 then 336 else 321) else (if i < 1071 then 337 else 338)))) else (if i < 1080 then (if i < 1076 then (if i < 1074 then (if i < 1073 then 337 else 333) else (if i < 1075 then 333 else 335)) else (if i < 1078 then (if i < 1077 then 335 else 336) else (if i < 1079 then 336 else 337))) else (if i < 1084 then (if i < 1082 then (if i < 1081 then 339 else 317) else (if i < 1083 then 340 else 341)) else (if i < 1086 then (if i < 1085 then 342 else 343) else (if i < 1087 then 344 else 327)))))

private def labelValue_b34 (i : ℕ) : ℕ :=
  (if i < 1104 then (if i < 1096 then (if i < 1092 then (if i < 1090 then (if i < 1089 then 344 else 339) else (if i < 1091 then 339 else 340)) else (if i < 1094 then (if i < 1093 then 340 else 342) else (if i < 1095 then 342 else 344))) else (if i < 1100 then (if i < 1098 then (if i < 1097 then 334 else 315) else (if i < 1099 then 317 else 334)) else (if i < 1102 then (if i < 1101 then 334 else 338) else (if i < 1103 then 345 else 338)))) else (if i < 1112 then (if i < 1108 then (if i < 1106 then (if i < 1105 then 334 else 345) else (if i < 1107 then 345 else 343)) else (if i < 1110 then (if i < 1109 then 341 else 345) else (if i < 1111 then 341 else 343))) else (if i < 1116 then (if i < 1114 then (if i < 1113 then 327 else 343) else (if i < 1115 then 343 else 321)) else (if i < 1118 then (if i < 1117 then 346 else 347) else (if i < 1119 then 325 else 348)))))

private def labelValue_b35 (i : ℕ) : ℕ :=
  (if i < 1136 then (if i < 1128 then (if i < 1124 then (if i < 1122 then (if i < 1121 then 349 else 350) else (if i < 1123 then 351 else 352)) else (if i < 1126 then (if i < 1125 then 347 else 352) else (if i < 1127 then 348 else 347))) else (if i < 1132 then (if i < 1130 then (if i < 1129 then 350 else 348) else (if i < 1131 then 352 else 350)) else (if i < 1134 then (if i < 1133 then 323 else 353) else (if i < 1135 then 354 else 355)))) else (if i < 1144 then (if i < 1140 then (if i < 1138 then (if i < 1137 then 356 else 357) else (if i < 1139 then 358 else 359)) else (if i < 1142 then (if i < 1141 then 353 else 359) else (if i < 1143 then 355 else 353))) else (if i < 1148 then (if i < 1146 then (if i < 1145 then 357 else 355) else (if i < 1147 then 359 else 357)) else (if i < 1150 then (if i < 1149 then 325 else 346) else (if i < 1151 then 346 else 323)))))

private def labelValue_b36 (i : ℕ) : ℕ :=
  (if i < 1168 then (if i < 1160 then (if i < 1156 then (if i < 1154 then (if i < 1153 then 351 else 346) else (if i < 1155 then 351 else 360)) else (if i < 1158 then (if i < 1157 then 360 else 346) else (if i < 1159 then 356 else 360))) else (if i < 1164 then (if i < 1162 then (if i < 1161 then 360 else 354) else (if i < 1163 then 356 else 354)) else (if i < 1166 then (if i < 1165 then 356 else 358) else (if i < 1167 then 349 else 356)))) else (if i < 1176 then (if i < 1172 then (if i < 1170 then (if i < 1169 then 361 else 7) else (if i < 1171 then 362 else 363)) else (if i < 1174 then (if i < 1173 then 364 else 365) else (if i < 1175 then 366 else 367))) else (if i < 1180 then (if i < 1178 then (if i < 1177 then 366 else 361) else (if i < 1179 then 361 else 362)) else (if i < 1182 then (if i < 1181 then 362 else 364) else (if i < 1183 then 364 else 366)))))

private def labelValue_b37 (i : ℕ) : ℕ :=
  (if i < 1200 then (if i < 1192 then (if i < 1188 then (if i < 1186 then (if i < 1185 then 368 else 369) else (if i < 1187 then 370 else 371)) else (if i < 1190 then (if i < 1189 then 372 else 373) else (if i < 1191 then 374 else 375))) else (if i < 1196 then (if i < 1194 then (if i < 1193 then 374 else 368) else (if i < 1195 then 368 else 370)) else (if i < 1198 then (if i < 1197 then 370 else 372) else (if i < 1199 then 372 else 374)))) else (if i < 1208 then (if i < 1204 then (if i < 1202 then (if i < 1201 then 376 else 377) else (if i < 1203 then 378 else 371)) else (if i < 1206 then (if i < 1205 then 379 else 363) else (if i < 1207 then 380 else 7))) else (if i < 1212 then (if i < 1210 then (if i < 1209 then 380 else 376) else (if i < 1211 then 376 else 378)) else (if i < 1214 then (if i < 1213 then 378 else 379) else (if i < 1215 then 379 else 380)))))

private def labelValue_b38 (i : ℕ) : ℕ :=
  (if i < 1232 then (if i < 1224 then (if i < 1220 then (if i < 1218 then (if i < 1217 then 381 else 382) else (if i < 1219 then 383 else 363)) else (if i < 1222 then (if i < 1221 then 384 else 369) else (if i < 1223 then 385 else 386))) else (if i < 1228 then (if i < 1226 then (if i < 1225 then 385 else 381) else (if i < 1227 then 381 else 383)) else (if i < 1230 then (if i < 1229 then 383 else 384) else (if i < 1231 then 384 else 385)))) else (if i < 1240 then (if i < 1236 then (if i < 1234 then (if i < 1233 then 387 else 365) else (if i < 1235 then 388 else 389)) else (if i < 1238 then (if i < 1237 then 390 else 391) else (if i < 1239 then 392 else 375))) else (if i < 1244 then (if i < 1242 then (if i < 1241 then 392 else 387) else (if i < 1243 then 387 else 388)) else (if i < 1246 then (if i < 1245 then 388 else 390) else (if i < 1247 then 390 else 392)))))

private def labelValue_b39 (i : ℕ) : ℕ :=
  (if i < 1264 then (if i < 1256 then (if i < 1252 then (if i < 1250 then (if i < 1249 then 382 else 363) else (if i < 1251 then 365 else 382)) else (if i < 1254 then (if i < 1253 then 382 else 386) else (if i < 1255 then 393 else 386))) else (if i < 1260 then (if i < 1258 then (if i < 1257 then 382 else 393) else (if i < 1259 then 393 else 391)) else (if i < 1262 then (if i < 1261 then 389 else 393) else (if i < 1263 then 389 else 391)))) else (if i < 1272 then (if i < 1268 then (if i < 1266 then (if i < 1265 then 375 else 391) else (if i < 1267 then 391 else 369)) else (if i < 1270 then (if i < 1269 then 394 else 395) else (if i < 1271 then 373 else 396))) else (if i < 1276 then (if i < 1274 then (if i < 1273 then 397 else 398) else (if i < 1275 then 399 else 400)) else (if i < 1278 then (if i < 1277 then 395 else 400) else (if i < 1279 then 396 else 395)))))

private def labelValue_b40 (i : ℕ) : ℕ :=
  (if i < 1296 then (if i < 1288 then (if i < 1284 then (if i < 1282 then (if i < 1281 then 398 else 396) else (if i < 1283 then 400 else 398)) else (if i < 1286 then (if i < 1285 then 371 else 401) else (if i < 1287 then 402 else 403))) else (if i < 1292 then (if i < 1290 then (if i < 1289 then 404 else 405) else (if i < 1291 then 406 else 407)) else (if i < 1294 then (if i < 1293 then 401 else 407) else (if i < 1295 then 403 else 401)))) else (if i < 1304 then (if i < 1300 then (if i < 1298 then (if i < 1297 then 405 else 403) else (if i < 1299 then 407 else 405)) else (if i < 1302 then (if i < 1301 then 373 else 394) else (if i < 1303 then 394 else 371))) else (if i < 1308 then (if i < 1306 then (if i < 1305 then 399 else 394) else (if i < 1307 then 399 else 408)) else (if i < 1310 then (if i < 1309 then 408 else 394) else (if i < 1311 then 404 else 408)))))

private def labelValue_b41 (i : ℕ) : ℕ :=
  (if i < 1328 then (if i < 1320 then (if i < 1316 then (if i < 1314 then (if i < 1313 then 408 else 402) else (if i < 1315 then 404 else 402)) else (if i < 1318 then (if i < 1317 then 404 else 406) else (if i < 1319 then 397 else 404))) else (if i < 1324 then (if i < 1322 then (if i < 1321 then 409 else 410) else (if i < 1323 then 411 else 412)) else (if i < 1326 then (if i < 1325 then 413 else 414) else (if i < 1327 then 415 else 99)))) else (if i < 1336 then (if i < 1332 then (if i < 1330 then (if i < 1329 then 415 else 409) else (if i < 1331 then 409 else 411)) else (if i < 1334 then (if i < 1333 then 411 else 413) else (if i < 1335 then 413 else 415))) else (if i < 1340 then (if i < 1338 then (if i < 1337 then 416 else 417) else (if i < 1339 then 418 else 419)) else (if i < 1342 then (if i < 1341 then 420 else 421) else (if i < 1343 then 422 else 423)))))

private def labelValue_b42 (i : ℕ) : ℕ :=
  (if i < 1360 then (if i < 1352 then (if i < 1348 then (if i < 1346 then (if i < 1345 then 422 else 416) else (if i < 1347 then 416 else 418)) else (if i < 1350 then (if i < 1349 then 418 else 420) else (if i < 1351 then 420 else 422))) else (if i < 1356 then (if i < 1354 then (if i < 1353 then 424 else 425) else (if i < 1355 then 426 else 419)) else (if i < 1358 then (if i < 1357 then 427 else 412) else (if i < 1359 then 428 else 410)))) else (if i < 1368 then (if i < 1364 then (if i < 1362 then (if i < 1361 then 428 else 424) else (if i < 1363 then 424 else 426)) else (if i < 1366 then (if i < 1365 then 426 else 427) else (if i < 1367 then 427 else 428))) else (if i < 1372 then (if i < 1370 then (if i < 1369 then 429 else 430) else (if i < 1371 then 431 else 412)) else (if i < 1374 then (if i < 1373 then 432 else 417) else (if i < 1375 then 433 else 434)))))

private def labelValue_b43 (i : ℕ) : ℕ :=
  (if i < 1392 then (if i < 1384 then (if i < 1380 then (if i < 1378 then (if i < 1377 then 433 else 429) else (if i < 1379 then 429 else 431)) else (if i < 1382 then (if i < 1381 then 431 else 432) else (if i < 1383 then 432 else 433))) else (if i < 1388 then (if i < 1386 then (if i < 1385 then 435 else 414) else (if i < 1387 then 436 else 437)) else (if i < 1390 then (if i < 1389 then 438 else 439) else (if i < 1391 then 440 else 423)))) else (if i < 1400 then (if i < 1396 then (if i < 1394 then (if i < 1393 then 440 else 435) else (if i < 1395 then 435 else 436)) else (if i < 1398 then (if i < 1397 then 436 else 438) else (if i < 1399 then 438 else 440))) else (if i < 1404 then (if i < 1402 then (if i < 1401 then 430 else 412) else (if i < 1403 then 414 else 430)) else (if i < 1406 then (if i < 1405 then 430 else 434) else (if i < 1407 then 441 else 434)))))

private def labelValue_b44 (i : ℕ) : ℕ :=
  (if i < 1424 then (if i < 1416 then (if i < 1412 then (if i < 1410 then (if i < 1409 then 430 else 441) else (if i < 1411 then 441 else 439)) else (if i < 1414 then (if i < 1413 then 437 else 441) else (if i < 1415 then 437 else 439))) else (if i < 1420 then (if i < 1418 then (if i < 1417 then 423 else 439) else (if i < 1419 then 439 else 417)) else (if i < 1422 then (if i < 1421 then 442 else 443) else (if i < 1423 then 421 else 444)))) else (if i < 1432 then (if i < 1428 then (if i < 1426 then (if i < 1425 then 445 else 446) else (if i < 1427 then 447 else 448)) else (if i < 1430 then (if i < 1429 then 443 else 448) else (if i < 1431 then 444 else 443))) else (if i < 1436 then (if i < 1434 then (if i < 1433 then 446 else 444) else (if i < 1435 then 448 else 446)) else (if i < 1438 then (if i < 1437 then 419 else 449) else (if i < 1439 then 450 else 451)))))

private def labelValue_b45 (i : ℕ) : ℕ :=
  (if i < 1456 then (if i < 1448 then (if i < 1444 then (if i < 1442 then (if i < 1441 then 452 else 453) else (if i < 1443 then 349 else 454)) else (if i < 1446 then (if i < 1445 then 449 else 454) else (if i < 1447 then 451 else 449))) else (if i < 1452 then (if i < 1450 then (if i < 1449 then 453 else 451) else (if i < 1451 then 454 else 453)) else (if i < 1454 then (if i < 1453 then 421 else 442) else (if i < 1455 then 442 else 419)))) else (if i < 1464 then (if i < 1460 then (if i < 1458 then (if i < 1457 then 447 else 442) else (if i < 1459 then 447 else 455)) else (if i < 1462 then (if i < 1461 then 455 else 442) else (if i < 1463 then 452 else 455))) else (if i < 1468 then (if i < 1466 then (if i < 1465 then 455 else 450) else (if i < 1467 then 452 else 450)) else (if i < 1470 then (if i < 1469 then 452 else 349) else (if i < 1471 then 445 else 452)))))

private def labelValue_b46 (i : ℕ) : ℕ :=
  (if i < 1488 then (if i < 1480 then (if i < 1476 then (if i < 1474 then (if i < 1473 then 397 else 456) else (if i < 1475 then 375 else 457)) else (if i < 1478 then (if i < 1477 then 458 else 459) else (if i < 1479 then 329 else 459))) else (if i < 1484 then (if i < 1482 then (if i < 1481 then 456 else 329) else (if i < 1483 then 457 else 456)) else (if i < 1486 then (if i < 1485 then 459 else 457) else (if i < 1487 then 406 else 460)))) else (if i < 1496 then (if i < 1492 then (if i < 1490 then (if i < 1489 then 423 else 461) else (if i < 1491 then 462 else 463)) else (if i < 1494 then (if i < 1493 then 377 else 463) else (if i < 1495 then 460 else 377))) else (if i < 1500 then (if i < 1498 then (if i < 1497 then 461 else 460) else (if i < 1499 then 463 else 461)) else (if i < 1502 then (if i < 1501 then 349 else 464) else (if i < 1503 then 327 else 465)))))

private def labelValue_b47 (i : ℕ) : ℕ :=
  (if i < 1520 then (if i < 1512 then (if i < 1508 then (if i < 1506 then (if i < 1505 then 466 else 467) else (if i < 1507 then 425 else 467)) else (if i < 1510 then (if i < 1509 then 464 else 425) else (if i < 1511 then 465 else 464))) else (if i < 1516 then (if i < 1514 then (if i < 1513 then 467 else 465) else (if i < 1515 then 468 else 397)) else (if i < 1518 then (if i < 1517 then 468 else 406) else (if i < 1519 then 468 else 349)))) else (if i < 1528 then (if i < 1524 then (if i < 1522 then (if i < 1521 then 397 else 358) else (if i < 1523 then 445 else 406)) else (if i < 1526 then (if i < 1525 then 469 else 470) else (if i < 1527 then 471 else 472))) else (if i < 1532 then (if i < 1530 then (if i < 1529 then 473 else 474) else (if i < 1531 then 475 else 7)) else (if i < 1534 then (if i < 1533 then 475 else 469) else (if i < 1535 then 469 else 471)))))

private def labelValue_b48 (i : ℕ) : ℕ :=
  (if i < 1552 then (if i < 1544 then (if i < 1540 then (if i < 1538 then (if i < 1537 then 471 else 473) else (if i < 1539 then 473 else 475)) else (if i < 1542 then (if i < 1541 then 476 else 477) else (if i < 1543 then 478 else 479))) else (if i < 1548 then (if i < 1546 then (if i < 1545 then 480 else 481) else (if i < 1547 then 482 else 483)) else (if i < 1550 then (if i < 1549 then 482 else 476) else (if i < 1551 then 476 else 478)))) else (if i < 1560 then (if i < 1556 then (if i < 1554 then (if i < 1553 then 478 else 480) else (if i < 1555 then 480 else 482)) else (if i < 1558 then (if i < 1557 then 484 else 485) else (if i < 1559 then 486 else 479))) else (if i < 1564 then (if i < 1562 then (if i < 1561 then 487 else 472) else (if i < 1563 then 488 else 470)) else (if i < 1566 then (if i < 1565 then 488 else 484) else (if i < 1567 then 484 else 486)))))

private def labelValue_b49 (i : ℕ) : ℕ :=
  (if i < 1584 then (if i < 1576 then (if i < 1572 then (if i < 1570 then (if i < 1569 then 486 else 487) else (if i < 1571 then 487 else 488)) else (if i < 1574 then (if i < 1573 then 489 else 490) else (if i < 1575 then 491 else 472))) else (if i < 1580 then (if i < 1578 then (if i < 1577 then 492 else 477) else (if i < 1579 then 493 else 494)) else (if i < 1582 then (if i < 1581 then 493 else 489) else (if i < 1583 then 489 else 491)))) else (if i < 1592 then (if i < 1588 then (if i < 1586 then (if i < 1585 then 491 else 492) else (if i < 1587 then 492 else 493)) else (if i < 1590 then (if i < 1589 then 495 else 474) else (if i < 1591 then 496 else 497))) else (if i < 1596 then (if i < 1594 then (if i < 1593 then 498 else 499) else (if i < 1595 then 500 else 483)) else (if i < 1598 then (if i < 1597 then 500 else 495) else (if i < 1599 then 495 else 496)))))

private def labelValue_b50 (i : ℕ) : ℕ :=
  (if i < 1616 then (if i < 1608 then (if i < 1604 then (if i < 1602 then (if i < 1601 then 496 else 498) else (if i < 1603 then 498 else 500)) else (if i < 1606 then (if i < 1605 then 490 else 472) else (if i < 1607 then 474 else 490))) else (if i < 1612 then (if i < 1610 then (if i < 1609 then 490 else 494) else (if i < 1611 then 501 else 494)) else (if i < 1614 then (if i < 1613 then 490 else 501) else (if i < 1615 then 501 else 499)))) else (if i < 1624 then (if i < 1620 then (if i < 1618 then (if i < 1617 then 497 else 501) else (if i < 1619 then 497 else 499)) else (if i < 1622 then (if i < 1621 then 483 else 499) else (if i < 1623 then 499 else 477))) else (if i < 1628 then (if i < 1626 then (if i < 1625 then 502 else 503) else (if i < 1627 then 481 else 504)) else (if i < 1630 then (if i < 1629 then 505 else 506) else (if i < 1631 then 507 else 508)))))

private def labelValue_b51 (i : ℕ) : ℕ :=
  (if i < 1648 then (if i < 1640 then (if i < 1636 then (if i < 1634 then (if i < 1633 then 503 else 508) else (if i < 1635 then 504 else 503)) else (if i < 1638 then (if i < 1637 then 506 else 504) else (if i < 1639 then 508 else 506))) else (if i < 1644 then (if i < 1642 then (if i < 1641 then 479 else 509) else (if i < 1643 then 510 else 511)) else (if i < 1646 then (if i < 1645 then 512 else 513) else (if i < 1647 then 514 else 515)))) else (if i < 1656 then (if i < 1652 then (if i < 1650 then (if i < 1649 then 509 else 515) else (if i < 1651 then 511 else 509)) else (if i < 1654 then (if i < 1653 then 513 else 511) else (if i < 1655 then 515 else 513))) else (if i < 1660 then (if i < 1658 then (if i < 1657 then 481 else 502) else (if i < 1659 then 502 else 479)) else (if i < 1662 then (if i < 1661 then 507 else 502) else (if i < 1663 then 507 else 516)))))

private def labelValue_b52 (i : ℕ) : ℕ :=
  (if i < 1680 then (if i < 1672 then (if i < 1668 then (if i < 1666 then (if i < 1665 then 516 else 502) else (if i < 1667 then 512 else 516)) else (if i < 1670 then (if i < 1669 then 516 else 510) else (if i < 1671 then 512 else 510))) else (if i < 1676 then (if i < 1674 then (if i < 1673 then 512 else 514) else (if i < 1675 then 505 else 512)) else (if i < 1678 then (if i < 1677 then 517 else 319) else (if i < 1679 then 518 else 519)))) else (if i < 1688 then (if i < 1684 then (if i < 1682 then (if i < 1681 then 520 else 521) else (if i < 1683 then 522 else 470)) else (if i < 1686 then (if i < 1685 then 522 else 517) else (if i < 1687 then 517 else 518))) else (if i < 1692 then (if i < 1690 then (if i < 1689 then 518 else 520) else (if i < 1691 then 520 else 522)) else (if i < 1694 then (if i < 1693 then 523 else 524) else (if i < 1695 then 525 else 526)))))

private def labelValue_b53 (i : ℕ) : ℕ :=
  (if i < 1712 then (if i < 1704 then (if i < 1700 then (if i < 1698 then (if i < 1697 then 527 else 528) else (if i < 1699 then 529 else 530)) else (if i < 1702 then (if i < 1701 then 529 else 523) else (if i < 1703 then 523 else 525))) else (if i < 1708 then (if i < 1706 then (if i < 1705 then 525 else 527) else (if i < 1707 then 527 else 529)) else (if i < 1710 then (if i < 1709 then 531 else 532) else (if i < 1711 then 533 else 526)))) else (if i < 1720 then (if i < 1716 then (if i < 1714 then (if i < 1713 then 534 else 519) else (if i < 1715 then 535 else 319)) else (if i < 1718 then (if i < 1717 then 535 else 531) else (if i < 1719 then 531 else 533))) else (if i < 1724 then (if i < 1722 then (if i < 1721 then 533 else 534) else (if i < 1723 then 534 else 535)) else (if i < 1726 then (if i < 1725 then 536 else 537) else (if i < 1727 then 538 else 519)))))

private def labelValue_b54 (i : ℕ) : ℕ :=
  (if i < 1744 then (if i < 1736 then (if i < 1732 then (if i < 1730 then (if i < 1729 then 539 else 524) else (if i < 1731 then 540 else 541)) else (if i < 1734 then (if i < 1733 then 540 else 536) else (if i < 1735 then 536 else 538))) else (if i < 1740 then (if i < 1738 then (if i < 1737 then 538 else 539) else (if i < 1739 then 539 else 540)) else (if i < 1742 then (if i < 1741 then 542 else 521) else (if i < 1743 then 543 else 544)))) else (if i < 1752 then (if i < 1748 then (if i < 1746 then (if i < 1745 then 545 else 546) else (if i < 1747 then 547 else 530)) else (if i < 1750 then (if i < 1749 then 547 else 542) else (if i < 1751 then 542 else 543))) else (if i < 1756 then (if i < 1754 then (if i < 1753 then 543 else 545) else (if i < 1755 then 545 else 547)) else (if i < 1758 then (if i < 1757 then 537 else 519) else (if i < 1759 then 521 else 537)))))

private def labelValue_b55 (i : ℕ) : ℕ :=
  (if i < 1776 then (if i < 1768 then (if i < 1764 then (if i < 1762 then (if i < 1761 then 537 else 541) else (if i < 1763 then 548 else 541)) else (if i < 1766 then (if i < 1765 then 537 else 548) else (if i < 1767 then 548 else 546))) else (if i < 1772 then (if i < 1770 then (if i < 1769 then 544 else 548) else (if i < 1771 then 544 else 546)) else (if i < 1774 then (if i < 1773 then 530 else 546) else (if i < 1775 then 546 else 524)))) else (if i < 1784 then (if i < 1780 then (if i < 1778 then (if i < 1777 then 549 else 550) else (if i < 1779 then 528 else 551)) else (if i < 1782 then (if i < 1781 then 552 else 553) else (if i < 1783 then 554 else 555))) else (if i < 1788 then (if i < 1786 then (if i < 1785 then 550 else 555) else (if i < 1787 then 551 else 550)) else (if i < 1790 then (if i < 1789 then 553 else 551) else (if i < 1791 then 555 else 553)))))

private def labelValue_b56 (i : ℕ) : ℕ :=
  (if i < 1808 then (if i < 1800 then (if i < 1796 then (if i < 1794 then (if i < 1793 then 526 else 556) else (if i < 1795 then 557 else 558)) else (if i < 1798 then (if i < 1797 then 559 else 560) else (if i < 1799 then 561 else 562))) else (if i < 1804 then (if i < 1802 then (if i < 1801 then 556 else 562) else (if i < 1803 then 558 else 556)) else (if i < 1806 then (if i < 1805 then 560 else 558) else (if i < 1807 then 562 else 560)))) else (if i < 1816 then (if i < 1812 then (if i < 1810 then (if i < 1809 then 528 else 549) else (if i < 1811 then 549 else 526)) else (if i < 1814 then (if i < 1813 then 554 else 549) else (if i < 1815 then 554 else 563))) else (if i < 1820 then (if i < 1818 then (if i < 1817 then 563 else 549) else (if i < 1819 then 559 else 563)) else (if i < 1822 then (if i < 1821 then 563 else 557) else (if i < 1823 then 559 else 557)))))

private def labelValue_b57 (i : ℕ) : ℕ :=
  (if i < 1840 then (if i < 1832 then (if i < 1828 then (if i < 1826 then (if i < 1825 then 559 else 561) else (if i < 1827 then 552 else 559)) else (if i < 1830 then (if i < 1829 then 564 else 7) else (if i < 1831 then 565 else 566))) else (if i < 1836 then (if i < 1834 then (if i < 1833 then 567 else 568) else (if i < 1835 then 569 else 410)) else (if i < 1838 then (if i < 1837 then 569 else 564) else (if i < 1839 then 564 else 565)))) else (if i < 1848 then (if i < 1844 then (if i < 1842 then (if i < 1841 then 565 else 567) else (if i < 1843 then 567 else 569)) else (if i < 1846 then (if i < 1845 then 570 else 571) else (if i < 1847 then 572 else 573))) else (if i < 1852 then (if i < 1850 then (if i < 1849 then 574 else 575) else (if i < 1851 then 576 else 577)) else (if i < 1854 then (if i < 1853 then 576 else 570) else (if i < 1855 then 570 else 572)))))

private def labelValue_b58 (i : ℕ) : ℕ :=
  (if i < 1872 then (if i < 1864 then (if i < 1860 then (if i < 1858 then (if i < 1857 then 572 else 574) else (if i < 1859 then 574 else 576)) else (if i < 1862 then (if i < 1861 then 578 else 579) else (if i < 1863 then 580 else 573))) else (if i < 1868 then (if i < 1866 then (if i < 1865 then 581 else 566) else (if i < 1867 then 582 else 7)) else (if i < 1870 then (if i < 1869 then 582 else 578) else (if i < 1871 then 578 else 580)))) else (if i < 1880 then (if i < 1876 then (if i < 1874 then (if i < 1873 then 580 else 581) else (if i < 1875 then 581 else 582)) else (if i < 1878 then (if i < 1877 then 583 else 584) else (if i < 1879 then 585 else 566))) else (if i < 1884 then (if i < 1882 then (if i < 1881 then 586 else 571) else (if i < 1883 then 587 else 588)) else (if i < 1886 then (if i < 1885 then 587 else 583) else (if i < 1887 then 583 else 585)))))

private def labelValue_b59 (i : ℕ) : ℕ :=
  (if i < 1904 then (if i < 1896 then (if i < 1892 then (if i < 1890 then (if i < 1889 then 585 else 586) else (if i < 1891 then 586 else 587)) else (if i < 1894 then (if i < 1893 then 589 else 568) else (if i < 1895 then 590 else 591))) else (if i < 1900 then (if i < 1898 then (if i < 1897 then 592 else 593) else (if i < 1899 then 594 else 577)) else (if i < 1902 then (if i < 1901 then 594 else 589) else (if i < 1903 then 589 else 590)))) else (if i < 1912 then (if i < 1908 then (if i < 1906 then (if i < 1905 then 590 else 592) else (if i < 1907 then 592 else 594)) else (if i < 1910 then (if i < 1909 then 584 else 566) else (if i < 1911 then 568 else 584))) else (if i < 1916 then (if i < 1914 then (if i < 1913 then 584 else 588) else (if i < 1915 then 595 else 588)) else (if i < 1918 then (if i < 1917 then 584 else 595) else (if i < 1919 then 595 else 593)))))

private def labelValue_b60 (i : ℕ) : ℕ :=
  (if i < 1936 then (if i < 1928 then (if i < 1924 then (if i < 1922 then (if i < 1921 then 591 else 595) else (if i < 1923 then 591 else 593)) else (if i < 1926 then (if i < 1925 then 577 else 593) else (if i < 1927 then 593 else 571))) else (if i < 1932 then (if i < 1930 then (if i < 1929 then 596 else 597) else (if i < 1931 then 575 else 598)) else (if i < 1934 then (if i < 1933 then 599 else 600) else (if i < 1935 then 601 else 602)))) else (if i < 1944 then (if i < 1940 then (if i < 1938 then (if i < 1937 then 597 else 602) else (if i < 1939 then 598 else 597)) else (if i < 1942 then (if i < 1941 then 600 else 598) else (if i < 1943 then 602 else 600))) else (if i < 1948 then (if i < 1946 then (if i < 1945 then 573 else 603) else (if i < 1947 then 604 else 605)) else (if i < 1950 then (if i < 1949 then 606 else 607) else (if i < 1951 then 505 else 608)))))

private def labelValue_b61 (i : ℕ) : ℕ :=
  (if i < 1968 then (if i < 1960 then (if i < 1956 then (if i < 1954 then (if i < 1953 then 603 else 608) else (if i < 1955 then 605 else 603)) else (if i < 1958 then (if i < 1957 then 607 else 605) else (if i < 1959 then 608 else 607))) else (if i < 1964 then (if i < 1962 then (if i < 1961 then 575 else 596) else (if i < 1963 then 596 else 573)) else (if i < 1966 then (if i < 1965 then 601 else 596) else (if i < 1967 then 601 else 609)))) else (if i < 1976 then (if i < 1972 then (if i < 1970 then (if i < 1969 then 609 else 596) else (if i < 1971 then 606 else 609)) else (if i < 1974 then (if i < 1973 then 609 else 604) else (if i < 1975 then 606 else 604))) else (if i < 1980 then (if i < 1978 then (if i < 1977 then 606 else 505) else (if i < 1979 then 599 else 606)) else (if i < 1982 then (if i < 1981 then 552 else 610) else (if i < 1983 then 530 else 611)))))

private def labelValue_b62 (i : ℕ) : ℕ :=
  (if i < 2000 then (if i < 1992 then (if i < 1988 then (if i < 1986 then (if i < 1985 then 470 else 612) else (if i < 1987 then 485 else 612)) else (if i < 1990 then (if i < 1989 then 610 else 485) else (if i < 1991 then 611 else 610))) else (if i < 1996 then (if i < 1994 then (if i < 1993 then 612 else 611) else (if i < 1995 then 561 else 613)) else (if i < 1998 then (if i < 1997 then 577 else 614) else (if i < 1999 then 615 else 616)))) else (if i < 2008 then (if i < 2004 then (if i < 2002 then (if i < 2001 then 532 else 616) else (if i < 2003 then 613 else 532)) else (if i < 2006 then (if i < 2005 then 614 else 613) else (if i < 2007 then 616 else 614))) else (if i < 2012 then (if i < 2010 then (if i < 2009 then 505 else 617) else (if i < 2011 then 483 else 618)) else (if i < 2014 then (if i < 2013 then 7 else 619) else (if i < 2015 then 579 else 619)))))

private def labelValue_b63 (i : ℕ) : ℕ :=
  (if i < 2032 then (if i < 2024 then (if i < 2020 then (if i < 2018 then (if i < 2017 then 617 else 579) else (if i < 2019 then 618 else 617)) else (if i < 2022 then (if i < 2021 then 619 else 618) else (if i < 2023 then 620 else 552))) else (if i < 2028 then (if i < 2026 then (if i < 2025 then 620 else 561) else (if i < 2027 then 620 else 505)) else (if i < 2030 then (if i < 2029 then 552 else 514) else (if i < 2031 then 599 else 561)))) else (if i < 2040 then (if i < 2036 then (if i < 2034 then (if i < 2033 then 621 else 470) else (if i < 2035 then 622 else 623)) else (if i < 2038 then (if i < 2037 then 624 else 625) else (if i < 2039 then 626 else 319))) else (if i < 2044 then (if i < 2042 then (if i < 2041 then 626 else 621) else (if i < 2043 then 621 else 622)) else (if i < 2046 then (if i < 2045 then 622 else 624) else (if i < 2047 then 624 else 626)))))

private def labelValue_b64 (i : ℕ) : ℕ :=
  (if i < 2064 then (if i < 2056 then (if i < 2052 then (if i < 2050 then (if i < 2049 then 627 else 628) else (if i < 2051 then 629 else 630)) else (if i < 2054 then (if i < 2053 then 631 else 632) else (if i < 2055 then 633 else 634))) else (if i < 2060 then (if i < 2058 then (if i < 2057 then 633 else 627) else (if i < 2059 then 627 else 629)) else (if i < 2062 then (if i < 2061 then 629 else 631) else (if i < 2063 then 631 else 633)))) else (if i < 2072 then (if i < 2068 then (if i < 2066 then (if i < 2065 then 635 else 636) else (if i < 2067 then 637 else 630)) else (if i < 2070 then (if i < 2069 then 638 else 623) else (if i < 2071 then 639 else 470))) else (if i < 2076 then (if i < 2074 then (if i < 2073 then 639 else 635) else (if i < 2075 then 635 else 637)) else (if i < 2078 then (if i < 2077 then 637 else 638) else (if i < 2079 then 638 else 639)))))

private def labelValue_b65 (i : ℕ) : ℕ :=
  (if i < 2096 then (if i < 2088 then (if i < 2084 then (if i < 2082 then (if i < 2081 then 640 else 641) else (if i < 2083 then 642 else 623)) else (if i < 2086 then (if i < 2085 then 643 else 628) else (if i < 2087 then 644 else 645))) else (if i < 2092 then (if i < 2090 then (if i < 2089 then 644 else 640) else (if i < 2091 then 640 else 642)) else (if i < 2094 then (if i < 2093 then 642 else 643) else (if i < 2095 then 643 else 644)))) else (if i < 2104 then (if i < 2100 then (if i < 2098 then (if i < 2097 then 646 else 625) else (if i < 2099 then 647 else 648)) else (if i < 2102 then (if i < 2101 then 649 else 650) else (if i < 2103 then 651 else 634))) else (if i < 2108 then (if i < 2106 then (if i < 2105 then 651 else 646) else (if i < 2107 then 646 else 647)) else (if i < 2110 then (if i < 2109 then 647 else 649) else (if i < 2111 then 649 else 651)))))

private def labelValue_b66 (i : ℕ) : ℕ :=
  (if i < 2128 then (if i < 2120 then (if i < 2116 then (if i < 2114 then (if i < 2113 then 641 else 623) else (if i < 2115 then 625 else 641)) else (if i < 2118 then (if i < 2117 then 641 else 645) else (if i < 2119 then 652 else 645))) else (if i < 2124 then (if i < 2122 then (if i < 2121 then 641 else 652) else (if i < 2123 then 652 else 650)) else (if i < 2126 then (if i < 2125 then 648 else 652) else (if i < 2127 then 648 else 650)))) else (if i < 2136 then (if i < 2132 then (if i < 2130 then (if i < 2129 then 634 else 650) else (if i < 2131 then 650 else 628)) else (if i < 2134 then (if i < 2133 then 653 else 654) else (if i < 2135 then 632 else 655))) else (if i < 2140 then (if i < 2138 then (if i < 2137 then 656 else 657) else (if i < 2139 then 658 else 659)) else (if i < 2142 then (if i < 2141 then 654 else 659) else (if i < 2143 then 655 else 654)))))

private def labelValue_b67 (i : ℕ) : ℕ :=
  (if i < 2160 then (if i < 2152 then (if i < 2148 then (if i < 2146 then (if i < 2145 then 657 else 655) else (if i < 2147 then 659 else 657)) else (if i < 2150 then (if i < 2149 then 630 else 660) else (if i < 2151 then 661 else 662))) else (if i < 2156 then (if i < 2154 then (if i < 2153 then 663 else 664) else (if i < 2155 then 665 else 666)) else (if i < 2158 then (if i < 2157 then 660 else 666) else (if i < 2159 then 662 else 660)))) else (if i < 2168 then (if i < 2164 then (if i < 2162 then (if i < 2161 then 664 else 662) else (if i < 2163 then 666 else 664)) else (if i < 2166 then (if i < 2165 then 632 else 653) else (if i < 2167 then 653 else 630))) else (if i < 2172 then (if i < 2170 then (if i < 2169 then 658 else 653) else (if i < 2171 then 658 else 667)) else (if i < 2174 then (if i < 2173 then 667 else 653) else (if i < 2175 then 663 else 667)))))

private def labelValue_b68 (i : ℕ) : ℕ :=
  (if i < 2192 then (if i < 2184 then (if i < 2180 then (if i < 2178 then (if i < 2177 then 667 else 661) else (if i < 2179 then 663 else 661)) else (if i < 2182 then (if i < 2181 then 663 else 665) else (if i < 2183 then 656 else 663))) else (if i < 2188 then (if i < 2186 then (if i < 2185 then 668 else 367) else (if i < 2187 then 669 else 670)) else (if i < 2190 then (if i < 2189 then 671 else 672) else (if i < 2191 then 673 else 470)))) else (if i < 2200 then (if i < 2196 then (if i < 2194 then (if i < 2193 then 673 else 668) else (if i < 2195 then 668 else 669)) else (if i < 2198 then (if i < 2197 then 669 else 671) else (if i < 2199 then 671 else 673))) else (if i < 2204 then (if i < 2202 then (if i < 2201 then 674 else 675) else (if i < 2203 then 676 else 677)) else (if i < 2206 then (if i < 2205 then 678 else 679) else (if i < 2207 then 680 else 681)))))

private def labelValue_b69 (i : ℕ) : ℕ :=
  (if i < 2224 then (if i < 2216 then (if i < 2212 then (if i < 2210 then (if i < 2209 then 680 else 674) else (if i < 2211 then 674 else 676)) else (if i < 2214 then (if i < 2213 then 676 else 678) else (if i < 2215 then 678 else 680))) else (if i < 2220 then (if i < 2218 then (if i < 2217 then 682 else 683) else (if i < 2219 then 684 else 677)) else (if i < 2222 then (if i < 2221 then 685 else 670) else (if i < 2223 then 686 else 367)))) else (if i < 2232 then (if i < 2228 then (if i < 2226 then (if i < 2225 then 686 else 682) else (if i < 2227 then 682 else 684)) else (if i < 2230 then (if i < 2229 then 684 else 685) else (if i < 2231 then 685 else 686))) else (if i < 2236 then (if i < 2234 then (if i < 2233 then 687 else 688) else (if i < 2235 then 689 else 670)) else (if i < 2238 then (if i < 2237 then 690 else 675) else (if i < 2239 then 691 else 692)))))

private def labelValue_b70 (i : ℕ) : ℕ :=
  (if i < 2256 then (if i < 2248 then (if i < 2244 then (if i < 2242 then (if i < 2241 then 691 else 687) else (if i < 2243 then 687 else 689)) else (if i < 2246 then (if i < 2245 then 689 else 690) else (if i < 2247 then 690 else 691))) else (if i < 2252 then (if i < 2250 then (if i < 2249 then 693 else 672) else (if i < 2251 then 694 else 695)) else (if i < 2254 then (if i < 2253 then 696 else 697) else (if i < 2255 then 698 else 681)))) else (if i < 2264 then (if i < 2260 then (if i < 2258 then (if i < 2257 then 698 else 693) else (if i < 2259 then 693 else 694)) else (if i < 2262 then (if i < 2261 then 694 else 696) else (if i < 2263 then 696 else 698))) else (if i < 2268 then (if i < 2266 then (if i < 2265 then 688 else 670) else (if i < 2267 then 672 else 688)) else (if i < 2270 then (if i < 2269 then 688 else 692) else (if i < 2271 then 699 else 692)))))

private def labelValue_b71 (i : ℕ) : ℕ :=
  (if i < 2288 then (if i < 2280 then (if i < 2276 then (if i < 2274 then (if i < 2273 then 688 else 699) else (if i < 2275 then 699 else 697)) else (if i < 2278 then (if i < 2277 then 695 else 699) else (if i < 2279 then 695 else 697))) else (if i < 2284 then (if i < 2282 then (if i < 2281 then 681 else 697) else (if i < 2283 then 697 else 675)) else (if i < 2286 then (if i < 2285 then 700 else 701) else (if i < 2287 then 679 else 702)))) else (if i < 2296 then (if i < 2292 then (if i < 2290 then (if i < 2289 then 703 else 704) else (if i < 2291 then 705 else 706)) else (if i < 2294 then (if i < 2293 then 701 else 706) else (if i < 2295 then 702 else 701))) else (if i < 2300 then (if i < 2298 then (if i < 2297 then 704 else 702) else (if i < 2299 then 706 else 704)) else (if i < 2302 then (if i < 2301 then 677 else 707) else (if i < 2303 then 708 else 709)))))

private def labelValue_b72 (i : ℕ) : ℕ :=
  (if i < 2320 then (if i < 2312 then (if i < 2308 then (if i < 2306 then (if i < 2305 then 710 else 711) else (if i < 2307 then 712 else 713)) else (if i < 2310 then (if i < 2309 then 707 else 713) else (if i < 2311 then 709 else 707))) else (if i < 2316 then (if i < 2314 then (if i < 2313 then 711 else 709) else (if i < 2315 then 713 else 711)) else (if i < 2318 then (if i < 2317 then 679 else 700) else (if i < 2319 then 700 else 677)))) else (if i < 2328 then (if i < 2324 then (if i < 2322 then (if i < 2321 then 705 else 700) else (if i < 2323 then 705 else 714)) else (if i < 2326 then (if i < 2325 then 714 else 700) else (if i < 2327 then 710 else 714))) else (if i < 2332 then (if i < 2330 then (if i < 2329 then 714 else 708) else (if i < 2331 then 710 else 708)) else (if i < 2334 then (if i < 2333 then 710 else 712) else (if i < 2335 then 703 else 710)))))

private def labelValue_b73 (i : ℕ) : ℕ :=
  (if i < 2352 then (if i < 2344 then (if i < 2340 then (if i < 2338 then (if i < 2337 then 715 else 319) else (if i < 2339 then 716 else 717)) else (if i < 2342 then (if i < 2341 then 718 else 719) else (if i < 2343 then 720 else 313))) else (if i < 2348 then (if i < 2346 then (if i < 2345 then 720 else 715) else (if i < 2347 then 715 else 716)) else (if i < 2350 then (if i < 2349 then 716 else 718) else (if i < 2351 then 718 else 720)))) else (if i < 2360 then (if i < 2356 then (if i < 2354 then (if i < 2353 then 721 else 722) else (if i < 2355 then 723 else 724)) else (if i < 2358 then (if i < 2357 then 725 else 726) else (if i < 2359 then 727 else 728))) else (if i < 2364 then (if i < 2362 then (if i < 2361 then 727 else 721) else (if i < 2363 then 721 else 723)) else (if i < 2366 then (if i < 2365 then 723 else 725) else (if i < 2367 then 725 else 727)))))

private def labelValue_b74 (i : ℕ) : ℕ :=
  (if i < 2384 then (if i < 2376 then (if i < 2372 then (if i < 2370 then (if i < 2369 then 729 else 730) else (if i < 2371 then 731 else 724)) else (if i < 2374 then (if i < 2373 then 732 else 717) else (if i < 2375 then 733 else 319))) else (if i < 2380 then (if i < 2378 then (if i < 2377 then 733 else 729) else (if i < 2379 then 729 else 731)) else (if i < 2382 then (if i < 2381 then 731 else 732) else (if i < 2383 then 732 else 733)))) else (if i < 2392 then (if i < 2388 then (if i < 2386 then (if i < 2385 then 734 else 735) else (if i < 2387 then 736 else 717)) else (if i < 2390 then (if i < 2389 then 737 else 722) else (if i < 2391 then 738 else 739))) else (if i < 2396 then (if i < 2394 then (if i < 2393 then 738 else 734) else (if i < 2395 then 734 else 736)) else (if i < 2398 then (if i < 2397 then 736 else 737) else (if i < 2399 then 737 else 738)))))

private def labelValue_b75 (i : ℕ) : ℕ :=
  (if i < 2416 then (if i < 2408 then (if i < 2404 then (if i < 2402 then (if i < 2401 then 740 else 719) else (if i < 2403 then 741 else 742)) else (if i < 2406 then (if i < 2405 then 743 else 744) else (if i < 2407 then 745 else 728))) else (if i < 2412 then (if i < 2410 then (if i < 2409 then 745 else 740) else (if i < 2411 then 740 else 741)) else (if i < 2414 then (if i < 2413 then 741 else 743) else (if i < 2415 then 743 else 745)))) else (if i < 2424 then (if i < 2420 then (if i < 2418 then (if i < 2417 then 735 else 717) else (if i < 2419 then 719 else 735)) else (if i < 2422 then (if i < 2421 then 735 else 739) else (if i < 2423 then 746 else 739))) else (if i < 2428 then (if i < 2426 then (if i < 2425 then 735 else 746) else (if i < 2427 then 746 else 744)) else (if i < 2430 then (if i < 2429 then 742 else 746) else (if i < 2431 then 742 else 744)))))

private def labelValue_b76 (i : ℕ) : ℕ :=
  (if i < 2448 then (if i < 2440 then (if i < 2436 then (if i < 2434 then (if i < 2433 then 728 else 744) else (if i < 2435 then 744 else 722)) else (if i < 2438 then (if i < 2437 then 747 else 748) else (if i < 2439 then 726 else 749))) else (if i < 2444 then (if i < 2442 then (if i < 2441 then 750 else 751) else (if i < 2443 then 752 else 753)) else (if i < 2446 then (if i < 2445 then 748 else 753) else (if i < 2447 then 749 else 748)))) else (if i < 2456 then (if i < 2452 then (if i < 2450 then (if i < 2449 then 751 else 749) else (if i < 2451 then 753 else 751)) else (if i < 2454 then (if i < 2453 then 724 else 754) else (if i < 2455 then 755 else 756))) else (if i < 2460 then (if i < 2458 then (if i < 2457 then 757 else 758) else (if i < 2459 then 656 else 759)) else (if i < 2462 then (if i < 2461 then 754 else 759) else (if i < 2463 then 756 else 754)))))

private def labelValue_b77 (i : ℕ) : ℕ :=
  (if i < 2480 then (if i < 2472 then (if i < 2468 then (if i < 2466 then (if i < 2465 then 758 else 756) else (if i < 2467 then 759 else 758)) else (if i < 2470 then (if i < 2469 then 726 else 747) else (if i < 2471 then 747 else 724))) else (if i < 2476 then (if i < 2474 then (if i < 2473 then 752 else 747) else (if i < 2475 then 752 else 760)) else (if i < 2478 then (if i < 2477 then 760 else 747) else (if i < 2479 then 757 else 760)))) else (if i < 2488 then (if i < 2484 then (if i < 2482 then (if i < 2481 then 760 else 755) else (if i < 2483 then 757 else 755)) else (if i < 2486 then (if i < 2485 then 757 else 656) else (if i < 2487 then 750 else 757))) else (if i < 2492 then (if i < 2490 then (if i < 2489 then 703 else 761) else (if i < 2491 then 681 else 762)) else (if i < 2494 then (if i < 2493 then 470 else 763) else (if i < 2495 then 636 else 763)))))

private def labelValue_b78 (i : ℕ) : ℕ :=
  (if i < 2512 then (if i < 2504 then (if i < 2500 then (if i < 2498 then (if i < 2497 then 761 else 636) else (if i < 2499 then 762 else 761)) else (if i < 2502 then (if i < 2501 then 763 else 762) else (if i < 2503 then 712 else 764))) else (if i < 2508 then (if i < 2506 then (if i < 2505 then 728 else 765) else (if i < 2507 then 766 else 767)) else (if i < 2510 then (if i < 2509 then 683 else 767) else (if i < 2511 then 764 else 683)))) else (if i < 2520 then (if i < 2516 then (if i < 2514 then (if i < 2513 then 765 else 764) else (if i < 2515 then 767 else 765)) else (if i < 2518 then (if i < 2517 then 656 else 768) else (if i < 2519 then 634 else 769))) else (if i < 2524 then (if i < 2522 then (if i < 2521 then 319 else 770) else (if i < 2523 then 730 else 770)) else (if i < 2526 then (if i < 2525 then 768 else 730) else (if i < 2527 then 769 else 768)))))

private def labelValue_b79 (i : ℕ) : ℕ :=
  (if i < 2544 then (if i < 2536 then (if i < 2532 then (if i < 2530 then (if i < 2529 then 770 else 769) else (if i < 2531 then 771 else 703)) else (if i < 2534 then (if i < 2533 then 771 else 712) else (if i < 2535 then 771 else 656))) else (if i < 2540 then (if i < 2538 then (if i < 2537 then 703 else 665) else (if i < 2539 then 750 else 712)) else (if i < 2542 then (if i < 2541 then 772 else 773) else (if i < 2543 then 105 else 774)))) else (if i < 2552 then (if i < 2548 then (if i < 2546 then (if i < 2545 then 50 else 775) else (if i < 2547 then 152 else 775)) else (if i < 2550 then (if i < 2549 then 774 else 152) else (if i < 2551 then 773 else 774))) else (if i < 2556 then (if i < 2554 then (if i < 2553 then 775 else 773) else (if i < 2555 then 776 else 50)) else (if i < 2558 then (if i < 2557 then 777 else 105) else (if i < 2559 then 777 else 772)))))

private def labelValue_b80 (i : ℕ) : ℕ :=
  (if i < 2576 then (if i < 2568 then (if i < 2564 then (if i < 2562 then (if i < 2561 then 772 else 776) else (if i < 2563 then 776 else 778)) else (if i < 2566 then (if i < 2565 then 778 else 777) else (if i < 2567 then 50 else 779))) else (if i < 2572 then (if i < 2570 then (if i < 2569 then 207 else 780) else (if i < 2571 then 305 else 780)) else (if i < 2574 then (if i < 2573 then 779 else 305) else (if i < 2575 then 781 else 779)))) else (if i < 2584 then (if i < 2580 then (if i < 2578 then (if i < 2577 then 780 else 781) else (if i < 2579 then 56 else 782)) else (if i < 2582 then (if i < 2581 then 1 else 783) else (if i < 2583 then 148 else 783))) else (if i < 2588 then (if i < 2586 then (if i < 2585 then 782 else 148) else (if i < 2587 then 309 else 782)) else (if i < 2590 then (if i < 2589 then 783 else 309) else (if i < 2591 then 7 else 784)))))

private def labelValue_b81 (i : ℕ) : ℕ :=
  (if i < 2608 then (if i < 2600 then (if i < 2596 then (if i < 2594 then (if i < 2593 then 99 else 785) else (if i < 2595 then 156 else 785)) else (if i < 2598 then (if i < 2597 then 784 else 156) else (if i < 2599 then 462 else 784))) else (if i < 2604 then (if i < 2602 then (if i < 2601 then 785 else 462) else (if i < 2603 then 319 else 786)) else (if i < 2606 then (if i < 2605 then 410 else 787) else (if i < 2607 then 466 else 787)))) else (if i < 2616 then (if i < 2612 then (if i < 2610 then (if i < 2609 then 786 else 466) else (if i < 2611 then 615 else 786)) else (if i < 2614 then (if i < 2613 then 787 else 615) else (if i < 2615 then 367 else 788))) else (if i < 2620 then (if i < 2618 then (if i < 2617 then 313 else 789) else (if i < 2619 then 458 else 789)) else (if i < 2622 then (if i < 2621 then 788 else 458) else (if i < 2623 then 766 else 788)))))

private def labelValue_b82 (i : ℕ) : ℕ :=
  (if i < 2635 then (if i < 2629 then (if i < 2626 then (if i < 2625 then 789 else 766) else (if i < 2627 then 50 else (if i < 2628 then 790 else 778))) else (if i < 2632 then (if i < 2630 then 790 else (if i < 2631 then 105 else 790)) else (if i < 2633 then 99 else (if i < 2634 then 790 else 99)))) else (if i < 2640 then (if i < 2637 then (if i < 2636 then 790 else 99) else (if i < 2638 then 790 else (if i < 2639 then 207 else 790))) else (if i < 2643 then (if i < 2641 then 781 else (if i < 2642 then 790 else 50)) else (if i < 2644 then 790 else (if i < 2645 then 50 else 790)))))

private def labelValue_n0_0 (i : ℕ) : ℕ := if i < 32 then labelValue_b0 i else labelValue_b1 i

private def labelValue_n0_1 (i : ℕ) : ℕ := if i < 96 then labelValue_b2 i else labelValue_b3 i

private def labelValue_n0_2 (i : ℕ) : ℕ := if i < 160 then labelValue_b4 i else labelValue_b5 i

private def labelValue_n0_3 (i : ℕ) : ℕ := if i < 224 then labelValue_b6 i else labelValue_b7 i

private def labelValue_n0_4 (i : ℕ) : ℕ := if i < 288 then labelValue_b8 i else labelValue_b9 i

private def labelValue_n0_5 (i : ℕ) : ℕ := if i < 352 then labelValue_b10 i else labelValue_b11 i

private def labelValue_n0_6 (i : ℕ) : ℕ := if i < 416 then labelValue_b12 i else labelValue_b13 i

private def labelValue_n0_7 (i : ℕ) : ℕ := if i < 480 then labelValue_b14 i else labelValue_b15 i

private def labelValue_n0_8 (i : ℕ) : ℕ := if i < 544 then labelValue_b16 i else labelValue_b17 i

private def labelValue_n0_9 (i : ℕ) : ℕ := if i < 608 then labelValue_b18 i else labelValue_b19 i

private def labelValue_n0_10 (i : ℕ) : ℕ := if i < 672 then labelValue_b20 i else labelValue_b21 i

private def labelValue_n0_11 (i : ℕ) : ℕ := if i < 736 then labelValue_b22 i else labelValue_b23 i

private def labelValue_n0_12 (i : ℕ) : ℕ := if i < 800 then labelValue_b24 i else labelValue_b25 i

private def labelValue_n0_13 (i : ℕ) : ℕ := if i < 864 then labelValue_b26 i else labelValue_b27 i

private def labelValue_n0_14 (i : ℕ) : ℕ := if i < 928 then labelValue_b28 i else labelValue_b29 i

private def labelValue_n0_15 (i : ℕ) : ℕ := if i < 992 then labelValue_b30 i else labelValue_b31 i

private def labelValue_n0_16 (i : ℕ) : ℕ := if i < 1056 then labelValue_b32 i else labelValue_b33 i

private def labelValue_n0_17 (i : ℕ) : ℕ := if i < 1120 then labelValue_b34 i else labelValue_b35 i

private def labelValue_n0_18 (i : ℕ) : ℕ := if i < 1184 then labelValue_b36 i else labelValue_b37 i

private def labelValue_n0_19 (i : ℕ) : ℕ := if i < 1248 then labelValue_b38 i else labelValue_b39 i

private def labelValue_n0_20 (i : ℕ) : ℕ := if i < 1312 then labelValue_b40 i else labelValue_b41 i

private def labelValue_n0_21 (i : ℕ) : ℕ := if i < 1376 then labelValue_b42 i else labelValue_b43 i

private def labelValue_n0_22 (i : ℕ) : ℕ := if i < 1440 then labelValue_b44 i else labelValue_b45 i

private def labelValue_n0_23 (i : ℕ) : ℕ := if i < 1504 then labelValue_b46 i else labelValue_b47 i

private def labelValue_n0_24 (i : ℕ) : ℕ := if i < 1568 then labelValue_b48 i else labelValue_b49 i

private def labelValue_n0_25 (i : ℕ) : ℕ := if i < 1632 then labelValue_b50 i else labelValue_b51 i

private def labelValue_n0_26 (i : ℕ) : ℕ := if i < 1696 then labelValue_b52 i else labelValue_b53 i

private def labelValue_n0_27 (i : ℕ) : ℕ := if i < 1760 then labelValue_b54 i else labelValue_b55 i

private def labelValue_n0_28 (i : ℕ) : ℕ := if i < 1824 then labelValue_b56 i else labelValue_b57 i

private def labelValue_n0_29 (i : ℕ) : ℕ := if i < 1888 then labelValue_b58 i else labelValue_b59 i

private def labelValue_n0_30 (i : ℕ) : ℕ := if i < 1952 then labelValue_b60 i else labelValue_b61 i

private def labelValue_n0_31 (i : ℕ) : ℕ := if i < 2016 then labelValue_b62 i else labelValue_b63 i

private def labelValue_n0_32 (i : ℕ) : ℕ := if i < 2080 then labelValue_b64 i else labelValue_b65 i

private def labelValue_n0_33 (i : ℕ) : ℕ := if i < 2144 then labelValue_b66 i else labelValue_b67 i

private def labelValue_n0_34 (i : ℕ) : ℕ := if i < 2208 then labelValue_b68 i else labelValue_b69 i

private def labelValue_n0_35 (i : ℕ) : ℕ := if i < 2272 then labelValue_b70 i else labelValue_b71 i

private def labelValue_n0_36 (i : ℕ) : ℕ := if i < 2336 then labelValue_b72 i else labelValue_b73 i

private def labelValue_n0_37 (i : ℕ) : ℕ := if i < 2400 then labelValue_b74 i else labelValue_b75 i

private def labelValue_n0_38 (i : ℕ) : ℕ := if i < 2464 then labelValue_b76 i else labelValue_b77 i

private def labelValue_n0_39 (i : ℕ) : ℕ := if i < 2528 then labelValue_b78 i else labelValue_b79 i

private def labelValue_n0_40 (i : ℕ) : ℕ := if i < 2592 then labelValue_b80 i else labelValue_b81 i

private def labelValue_n1_0 (i : ℕ) : ℕ := if i < 64 then labelValue_n0_0 i else labelValue_n0_1 i

private def labelValue_n1_1 (i : ℕ) : ℕ := if i < 192 then labelValue_n0_2 i else labelValue_n0_3 i

private def labelValue_n1_2 (i : ℕ) : ℕ := if i < 320 then labelValue_n0_4 i else labelValue_n0_5 i

private def labelValue_n1_3 (i : ℕ) : ℕ := if i < 448 then labelValue_n0_6 i else labelValue_n0_7 i

private def labelValue_n1_4 (i : ℕ) : ℕ := if i < 576 then labelValue_n0_8 i else labelValue_n0_9 i

private def labelValue_n1_5 (i : ℕ) : ℕ := if i < 704 then labelValue_n0_10 i else labelValue_n0_11 i

private def labelValue_n1_6 (i : ℕ) : ℕ := if i < 832 then labelValue_n0_12 i else labelValue_n0_13 i

private def labelValue_n1_7 (i : ℕ) : ℕ := if i < 960 then labelValue_n0_14 i else labelValue_n0_15 i

private def labelValue_n1_8 (i : ℕ) : ℕ := if i < 1088 then labelValue_n0_16 i else labelValue_n0_17 i

private def labelValue_n1_9 (i : ℕ) : ℕ := if i < 1216 then labelValue_n0_18 i else labelValue_n0_19 i

private def labelValue_n1_10 (i : ℕ) : ℕ := if i < 1344 then labelValue_n0_20 i else labelValue_n0_21 i

private def labelValue_n1_11 (i : ℕ) : ℕ := if i < 1472 then labelValue_n0_22 i else labelValue_n0_23 i

private def labelValue_n1_12 (i : ℕ) : ℕ := if i < 1600 then labelValue_n0_24 i else labelValue_n0_25 i

private def labelValue_n1_13 (i : ℕ) : ℕ := if i < 1728 then labelValue_n0_26 i else labelValue_n0_27 i

private def labelValue_n1_14 (i : ℕ) : ℕ := if i < 1856 then labelValue_n0_28 i else labelValue_n0_29 i

private def labelValue_n1_15 (i : ℕ) : ℕ := if i < 1984 then labelValue_n0_30 i else labelValue_n0_31 i

private def labelValue_n1_16 (i : ℕ) : ℕ := if i < 2112 then labelValue_n0_32 i else labelValue_n0_33 i

private def labelValue_n1_17 (i : ℕ) : ℕ := if i < 2240 then labelValue_n0_34 i else labelValue_n0_35 i

private def labelValue_n1_18 (i : ℕ) : ℕ := if i < 2368 then labelValue_n0_36 i else labelValue_n0_37 i

private def labelValue_n1_19 (i : ℕ) : ℕ := if i < 2496 then labelValue_n0_38 i else labelValue_n0_39 i

private def labelValue_n1_20 (i : ℕ) : ℕ := if i < 2624 then labelValue_n0_40 i else labelValue_b82 i

private def labelValue_n2_0 (i : ℕ) : ℕ := if i < 128 then labelValue_n1_0 i else labelValue_n1_1 i

private def labelValue_n2_1 (i : ℕ) : ℕ := if i < 384 then labelValue_n1_2 i else labelValue_n1_3 i

private def labelValue_n2_2 (i : ℕ) : ℕ := if i < 640 then labelValue_n1_4 i else labelValue_n1_5 i

private def labelValue_n2_3 (i : ℕ) : ℕ := if i < 896 then labelValue_n1_6 i else labelValue_n1_7 i

private def labelValue_n2_4 (i : ℕ) : ℕ := if i < 1152 then labelValue_n1_8 i else labelValue_n1_9 i

private def labelValue_n2_5 (i : ℕ) : ℕ := if i < 1408 then labelValue_n1_10 i else labelValue_n1_11 i

private def labelValue_n2_6 (i : ℕ) : ℕ := if i < 1664 then labelValue_n1_12 i else labelValue_n1_13 i

private def labelValue_n2_7 (i : ℕ) : ℕ := if i < 1920 then labelValue_n1_14 i else labelValue_n1_15 i

private def labelValue_n2_8 (i : ℕ) : ℕ := if i < 2176 then labelValue_n1_16 i else labelValue_n1_17 i

private def labelValue_n2_9 (i : ℕ) : ℕ := if i < 2432 then labelValue_n1_18 i else labelValue_n1_19 i

private def labelValue_n3_0 (i : ℕ) : ℕ := if i < 256 then labelValue_n2_0 i else labelValue_n2_1 i

private def labelValue_n3_1 (i : ℕ) : ℕ := if i < 768 then labelValue_n2_2 i else labelValue_n2_3 i

private def labelValue_n3_2 (i : ℕ) : ℕ := if i < 1280 then labelValue_n2_4 i else labelValue_n2_5 i

private def labelValue_n3_3 (i : ℕ) : ℕ := if i < 1792 then labelValue_n2_6 i else labelValue_n2_7 i

private def labelValue_n3_4 (i : ℕ) : ℕ := if i < 2304 then labelValue_n2_8 i else labelValue_n2_9 i

private def labelValue_n4_0 (i : ℕ) : ℕ := if i < 512 then labelValue_n3_0 i else labelValue_n3_1 i

private def labelValue_n4_1 (i : ℕ) : ℕ := if i < 1536 then labelValue_n3_2 i else labelValue_n3_3 i

private def labelValue_n4_2 (i : ℕ) : ℕ := if i < 2560 then labelValue_n3_4 i else labelValue_n1_20 i

private def labelValue_n5_0 (i : ℕ) : ℕ := if i < 1024 then labelValue_n4_0 i else labelValue_n4_1 i

private def labelValue_n6_0 (i : ℕ) : ℕ := if i < 2048 then labelValue_n5_0 i else labelValue_n4_2 i

def labelValue (i : ℕ) : ℕ := labelValue_n6_0 i

end PlanarHom.ColoringMacroFaces.WireFramed
