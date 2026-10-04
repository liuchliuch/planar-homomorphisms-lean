import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.FanFramed
private def connectRankValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 3) else (if i < 3 then 6 else 4)) else (if i < 6 then (if i < 5 then 4 else 6) else (if i < 7 then 8 else 8))) else (if i < 12 then (if i < 10 then (if i < 9 then 4 else 4) else (if i < 11 then 8 else 8)) else (if i < 14 then (if i < 13 then 8 else 4) else (if i < 15 then 6 else 5)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 5 else 6) else (if i < 19 then 3 else 4)) else (if i < 22 then (if i < 21 then 4 else 5) else (if i < 23 then 5 else 4))) else (if i < 28 then (if i < 26 then (if i < 25 then 5 else 6) else (if i < 27 then 5 else 6)) else (if i < 30 then (if i < 29 then 5 else 4) else (if i < 31 then 4 else 5)))))

private def connectRankValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 6 else 5) else (if i < 35 then 6 else 4)) else (if i < 38 then (if i < 37 then 5 else 5) else (if i < 39 then 6 else 5))) else (if i < 44 then (if i < 42 then (if i < 41 then 6 else 6) else (if i < 43 then 6 else 6)) else (if i < 46 then (if i < 45 then 5 else 6) else (if i < 47 then 4 else 2)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 3 else 3) else (if i < 51 then 4 else 5)) else (if i < 54 then (if i < 53 then 6 else 4) else (if i < 55 then 5 else 5))) else (if i < 60 then (if i < 58 then (if i < 57 then 4 else 5) else (if i < 59 then 3 else 5)) else (if i < 62 then (if i < 61 then 5 else 6) else (if i < 63 then 6 else 5)))))

private def connectRankValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 6 else 6) else (if i < 67 then 6 else 5)) else (if i < 70 then (if i < 69 then 6 else 6) else (if i < 71 then 5 else 5))) else (if i < 76 then (if i < 74 then (if i < 73 then 4 else 4) else (if i < 75 then 5 else 6)) else (if i < 78 then (if i < 77 then 5 else 6) else (if i < 79 then 4 else 3)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 2 else 1) else (if i < 83 then 3 else 2)) else (if i < 86 then (if i < 85 then 1 else 2) else (if i < 87 then 2 else 3))) else (if i < 92 then (if i < 90 then (if i < 89 then 3 else 1) else (if i < 91 then 3 else 2)) else (if i < 94 then (if i < 93 then 3 else 3) else (if i < 95 then 3 else 2)))))

private def connectRankValue_b3 (i : ℕ) : ℕ :=
  (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 2 else 3) else (if i < 99 then 4 else 3)) else (if i < 102 then (if i < 101 then 3 else 2) else (if i < 103 then 3 else 3))) else (if i < 108 then (if i < 106 then (if i < 105 then 4 else 4) else (if i < 107 then 4 else 4)) else (if i < 110 then (if i < 109 then 4 else 5) else (if i < 111 then 3 else 4)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 6 else 2) else (if i < 115 then 3 else 7)) else (if i < 118 then (if i < 117 then 5 else 4) else (if i < 119 then 6 else 5))) else (if i < 124 then (if i < 122 then (if i < 121 then 4 else 5) else (if i < 123 then 5 else 6)) else (if i < 126 then (if i < 125 then 6 else 4) else (if i < 127 then 6 else 5)))))

private def connectRankValue_b4 (i : ℕ) : ℕ :=
  (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 6 else 6) else (if i < 131 then 6 else 5)) else (if i < 134 then (if i < 133 then 5 else 6) else (if i < 135 then 7 else 6))) else (if i < 140 then (if i < 138 then (if i < 137 then 6 else 5) else (if i < 139 then 6 else 6)) else (if i < 142 then (if i < 141 then 7 else 7) else (if i < 143 then 7 else 7)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 7 else 8) else (if i < 147 then 6 else 7)) else (if i < 150 then (if i < 149 then 8 else 6) else (if i < 151 then 5 else 7))) else (if i < 156 then (if i < 154 then (if i < 153 then 6 else 5) else (if i < 155 then 6 else 6)) else (if i < 158 then (if i < 157 then 7 else 7) else (if i < 159 then 5 else 7)))))

private def connectRankValue_b5 (i : ℕ) : ℕ :=
  (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 6 else 7) else (if i < 163 then 7 else 7)) else (if i < 166 then (if i < 165 then 6 else 6) else (if i < 167 then 7 else 8))) else (if i < 172 then (if i < 170 then (if i < 169 then 7 else 7) else (if i < 171 then 6 else 7)) else (if i < 174 then (if i < 173 then 7 else 8) else (if i < 175 then 8 else 8)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 8 else 8) else (if i < 179 then 9 else 7)) else (if i < 182 then (if i < 181 then 8 else 7) else (if i < 183 then 5 else 5))) else (if i < 188 then (if i < 186 then (if i < 185 then 6 else 6) else (if i < 187 then 5 else 6)) else (if i < 190 then (if i < 189 then 6 else 7) else (if i < 191 then 7 else 5)))))

private def connectRankValue_b6 (i : ℕ) : ℕ :=
  (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 7 else 6) else (if i < 195 then 7 else 7)) else (if i < 198 then (if i < 197 then 7 else 6) else (if i < 199 then 6 else 7))) else (if i < 204 then (if i < 202 then (if i < 201 then 8 else 7) else (if i < 203 then 7 else 6)) else (if i < 206 then (if i < 205 then 7 else 7) else (if i < 207 then 8 else 7)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 7 else 8) else (if i < 211 then 8 else 8)) else (if i < 214 then (if i < 213 then 7 else 7) else (if i < 215 then 6 else 6))) else (if i < 220 then (if i < 218 then (if i < 217 then 5 else 6) else (if i < 219 then 8 else 9)) else (if i < 222 then (if i < 221 then 7 else 8) else (if i < 223 then 7 else 8)))))

private def connectRankValue_b7 (i : ℕ) : ℕ :=
  (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 8 else 9) else (if i < 227 then 9 else 8)) else (if i < 230 then (if i < 229 then 9 else 8) else (if i < 231 then 9 else 9))) else (if i < 236 then (if i < 234 then (if i < 233 then 9 else 8) else (if i < 235 then 8 else 9)) else (if i < 238 then (if i < 237 then 10 else 9) else (if i < 239 then 9 else 8)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 9 else 7) else (if i < 243 then 8 else 7)) else (if i < 246 then (if i < 245 then 8 else 8) else (if i < 247 then 8 else 8))) else (if i < 252 then (if i < 250 then (if i < 249 then 8 else 8) else (if i < 251 then 6 else 4)) else (if i < 254 then (if i < 253 then 5 else 5) else (if i < 255 then 6 else 7)))))

private def connectRankValue_b8 (i : ℕ) : ℕ :=
  (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 8 else 6) else (if i < 259 then 7 else 7)) else (if i < 262 then (if i < 261 then 6 else 7) else (if i < 263 then 5 else 7))) else (if i < 268 then (if i < 266 then (if i < 265 then 7 else 8) else (if i < 267 then 8 else 7)) else (if i < 270 then (if i < 269 then 8 else 8) else (if i < 271 then 8 else 7)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 8 else 8) else (if i < 275 then 7 else 7)) else (if i < 278 then (if i < 277 then 6 else 6) else (if i < 279 then 7 else 8))) else (if i < 284 then (if i < 282 then (if i < 281 then 7 else 8) else (if i < 283 then 6 else 5)) else (if i < 286 then (if i < 285 then 6 else 5) else (if i < 287 then 7 else 6)))))

private def connectRankValue_b9 (i : ℕ) : ℕ :=
  (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 3 else 4) else (if i < 291 then 4 else 5)) else (if i < 294 then (if i < 293 then 5 else 4) else (if i < 295 then 5 else 6))) else (if i < 300 then (if i < 298 then (if i < 297 then 5 else 6) else (if i < 299 then 5 else 4)) else (if i < 302 then (if i < 301 then 4 else 5) else (if i < 303 then 6 else 5)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 6 else 4) else (if i < 307 then 5 else 5)) else (if i < 310 then (if i < 309 then 6 else 6) else (if i < 311 then 6 else 6))) else (if i < 316 then (if i < 314 then (if i < 313 then 6 else 7) else (if i < 315 then 5 else 7)) else (if i < 318 then (if i < 317 then 8 else 4) else (if i < 319 then 7 else 8)))))

private def connectRankValue_b10 (i : ℕ) : ℕ :=
  (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 6 else 7) else (if i < 323 then 7 else 8)) else (if i < 326 then (if i < 325 then 9 else 10) else (if i < 327 then 8 else 9))) else (if i < 332 then (if i < 330 then (if i < 329 then 9 else 8) else (if i < 331 then 9 else 7)) else (if i < 334 then (if i < 333 then 9 else 9) else (if i < 335 then 10 else 10)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 9 else 10) else (if i < 339 then 10 else 10)) else (if i < 342 then (if i < 341 then 9 else 10) else (if i < 343 then 10 else 9))) else (if i < 348 then (if i < 346 then (if i < 345 then 9 else 8) else (if i < 347 then 8 else 9)) else (if i < 350 then (if i < 349 then 10 else 9) else (if i < 351 then 10 else 8)))))

private def connectRankValue_b11 (i : ℕ) : ℕ :=
  (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 8 else 6) else (if i < 355 then 5 else 7)) else (if i < 358 then (if i < 357 then 6 else 5) else (if i < 359 then 6 else 6))) else (if i < 364 then (if i < 362 then (if i < 361 then 7 else 7) else (if i < 363 then 5 else 7)) else (if i < 366 then (if i < 365 then 6 else 7) else (if i < 367 then 7 else 7)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 6 else 6) else (if i < 371 then 7 else 8)) else (if i < 374 then (if i < 373 then 7 else 7) else (if i < 375 then 6 else 7))) else (if i < 380 then (if i < 378 then (if i < 377 then 7 else 8) else (if i < 379 then 8 else 8)) else (if i < 382 then (if i < 381 then 8 else 8) else (if i < 383 then 9 else 7)))))

private def connectRankValue_b12 (i : ℕ) : ℕ :=
  (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 8 else 9) else (if i < 387 then 8 else 7)) else (if i < 390 then (if i < 389 then 9 else 8) else (if i < 391 then 7 else 8))) else (if i < 396 then (if i < 394 then (if i < 393 then 8 else 9) else (if i < 395 then 9 else 7)) else (if i < 398 then (if i < 397 then 9 else 8) else (if i < 399 then 9 else 9)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 9 else 8) else (if i < 403 then 8 else 9)) else (if i < 406 then (if i < 405 then 10 else 9) else (if i < 407 then 9 else 8))) else (if i < 412 then (if i < 410 then (if i < 409 then 9 else 9) else (if i < 411 then 10 else 10)) else (if i < 414 then (if i < 413 then 10 else 10) else (if i < 415 then 10 else 11)))))

private def connectRankValue_b13 (i : ℕ) : ℕ :=
  (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 9 else 10) else (if i < 419 then 6 else 7)) else (if i < 422 then (if i < 421 then 9 else 10) else (if i < 423 then 8 else 9))) else (if i < 428 then (if i < 426 then (if i < 425 then 9 else 10) else (if i < 427 then 9 else 10)) else (if i < 430 then (if i < 429 then 10 else 11) else (if i < 431 then 11 else 9)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 11 else 9) else (if i < 435 then 11 else 11)) else (if i < 438 then (if i < 437 then 11 else 10) else (if i < 439 then 10 else 11))) else (if i < 444 then (if i < 442 then (if i < 441 then 12 else 11) else (if i < 443 then 11 else 10)) else (if i < 446 then (if i < 445 then 11 else 11) else (if i < 447 then 11 else 10)))))

private def connectRankValue_b14 (i : ℕ) : ℕ :=
  (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 10 else 11) else (if i < 451 then 12 else 11)) else (if i < 454 then (if i < 453 then 11 else 10) else (if i < 455 then 10 else 8))) else (if i < 460 then (if i < 458 then (if i < 457 then 7 else 9) else (if i < 459 then 8 else 7)) else (if i < 462 then (if i < 461 then 8 else 8) else (if i < 463 then 9 else 9)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 7 else 9) else (if i < 467 then 8 else 9)) else (if i < 470 then (if i < 469 then 9 else 9) else (if i < 471 then 8 else 8))) else (if i < 476 then (if i < 474 then (if i < 473 then 9 else 10) else (if i < 475 then 9 else 9)) else (if i < 478 then (if i < 477 then 8 else 9) else (if i < 479 then 9 else 10)))))

private def connectRankValue_b15 (i : ℕ) : ℕ :=
  (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 10 else 10) else (if i < 483 then 10 else 10)) else (if i < 486 then (if i < 485 then 11 else 9) else (if i < 487 then 10 else 11))) else (if i < 492 then (if i < 490 then (if i < 489 then 10 else 9) else (if i < 491 then 11 else 10)) else (if i < 494 then (if i < 493 then 9 else 10) else (if i < 495 then 10 else 11)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 11 else 9) else (if i < 499 then 11 else 10)) else (if i < 502 then (if i < 501 then 11 else 11) else (if i < 503 then 11 else 10))) else (if i < 508 then (if i < 506 then (if i < 505 then 10 else 11) else (if i < 507 then 12 else 11)) else (if i < 510 then (if i < 509 then 11 else 10) else (if i < 511 then 11 else 11)))))

private def connectRankValue_b16 (i : ℕ) : ℕ :=
  (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 12 else 12) else (if i < 515 then 12 else 12)) else (if i < 518 then (if i < 517 then 12 else 13) else (if i < 519 then 11 else 12))) else (if i < 524 then (if i < 522 then (if i < 521 then 8 else 9) else (if i < 523 then 10 else 4)) else (if i < 526 then (if i < 525 then 6 else 5) else (if i < 527 then 5 else 6)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 3 else 4) else (if i < 531 then 4 else 5)) else (if i < 534 then (if i < 533 then 5 else 4) else (if i < 535 then 5 else 6))) else (if i < 540 then (if i < 538 then (if i < 537 then 5 else 6) else (if i < 539 then 5 else 4)) else (if i < 542 then (if i < 541 then 4 else 5) else (if i < 543 then 6 else 5)))))

private def connectRankValue_b17 (i : ℕ) : ℕ :=
  (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then 6 else 4) else (if i < 547 then 5 else 5)) else (if i < 550 then (if i < 549 then 6 else 5) else (if i < 551 then 6 else 6))) else (if i < 556 then (if i < 554 then (if i < 553 then 6 else 6) else (if i < 555 then 5 else 6)) else (if i < 558 then (if i < 557 then 4 else 2) else (if i < 559 then 3 else 3)))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then 4 else 5) else (if i < 563 then 6 else 4)) else (if i < 566 then (if i < 565 then 5 else 5) else (if i < 567 then 4 else 5))) else (if i < 572 then (if i < 570 then (if i < 569 then 3 else 5) else (if i < 571 then 5 else 6)) else (if i < 574 then (if i < 573 then 6 else 5) else (if i < 575 then 6 else 6)))))

private def connectRankValue_b18 (i : ℕ) : ℕ :=
  (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then 6 else 5) else (if i < 579 then 6 else 6)) else (if i < 582 then (if i < 581 then 5 else 5) else (if i < 583 then 4 else 4))) else (if i < 588 then (if i < 586 then (if i < 585 then 5 else 6) else (if i < 587 then 5 else 6)) else (if i < 590 then (if i < 589 then 4 else 3) else (if i < 591 then 2 else 1)))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then 3 else 2) else (if i < 595 then 1 else 2)) else (if i < 598 then (if i < 597 then 2 else 3) else (if i < 599 then 3 else 1))) else (if i < 604 then (if i < 602 then (if i < 601 then 3 else 2) else (if i < 603 then 3 else 3)) else (if i < 606 then (if i < 605 then 3 else 2) else (if i < 607 then 2 else 3)))))

private def connectRankValue_b19 (i : ℕ) : ℕ :=
  (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then 4 else 3) else (if i < 611 then 3 else 2)) else (if i < 614 then (if i < 613 then 3 else 3) else (if i < 615 then 4 else 4))) else (if i < 620 then (if i < 618 then (if i < 617 then 4 else 4) else (if i < 619 then 4 else 5)) else (if i < 622 then (if i < 621 then 3 else 4) else (if i < 623 then 6 else 2)))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then 3 else 8) else (if i < 627 then 6 else 5)) else (if i < 630 then (if i < 629 then 7 else 6) else (if i < 631 then 5 else 6))) else (if i < 636 then (if i < 634 then (if i < 633 then 6 else 7) else (if i < 635 then 7 else 5)) else (if i < 638 then (if i < 637 then 7 else 6) else (if i < 639 then 7 else 7)))))

private def connectRankValue_b20 (i : ℕ) : ℕ :=
  (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then 7 else 6) else (if i < 643 then 6 else 7)) else (if i < 646 then (if i < 645 then 8 else 7) else (if i < 647 then 7 else 6))) else (if i < 652 then (if i < 650 then (if i < 649 then 7 else 7) else (if i < 651 then 8 else 8)) else (if i < 654 then (if i < 653 then 8 else 8) else (if i < 655 then 8 else 9)))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then 7 else 8) else (if i < 659 then 8 else 6)) else (if i < 662 then (if i < 661 then 7 else 7) else (if i < 663 then 8 else 7))) else (if i < 668 then (if i < 666 then (if i < 665 then 8 else 8) else (if i < 667 then 9 else 9)) else (if i < 670 then (if i < 669 then 7 else 9) else (if i < 671 then 7 else 9)))))

private def connectRankValue_b21 (i : ℕ) : ℕ :=
  (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then 9 else 9) else (if i < 675 then 8 else 8)) else (if i < 678 then (if i < 677 then 9 else 10) else (if i < 679 then 9 else 9))) else (if i < 684 then (if i < 682 then (if i < 681 then 8 else 9) else (if i < 683 then 9 else 9)) else (if i < 686 then (if i < 685 then 8 else 8) else (if i < 687 then 9 else 10)))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then 9 else 9) else (if i < 691 then 8 else 7)) else (if i < 694 then (if i < 693 then 6 else 5) else (if i < 695 then 7 else 6))) else (if i < 700 then (if i < 698 then (if i < 697 then 5 else 6) else (if i < 699 then 6 else 7)) else (if i < 702 then (if i < 701 then 7 else 5) else (if i < 703 then 7 else 6)))))

private def connectRankValue_b22 (i : ℕ) : ℕ :=
  (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then 7 else 7) else (if i < 707 then 7 else 6)) else (if i < 710 then (if i < 709 then 6 else 7) else (if i < 711 then 8 else 7))) else (if i < 716 then (if i < 714 then (if i < 713 then 7 else 6) else (if i < 715 then 7 else 7)) else (if i < 718 then (if i < 717 then 8 else 8) else (if i < 719 then 8 else 8)))) else (if i < 728 then (if i < 724 then (if i < 722 then (if i < 721 then 8 else 9) else (if i < 723 then 7 else 8)) else (if i < 726 then (if i < 725 then 7 else 6) else (if i < 727 then 6 else 8))) else (if i < 732 then (if i < 730 then (if i < 729 then 10 else 9) else (if i < 731 then 9 else 10)) else (if i < 734 then (if i < 733 then 7 else 8) else (if i < 735 then 8 else 9)))))

private def connectRankValue_b23 (i : ℕ) : ℕ :=
  (if i < 752 then (if i < 744 then (if i < 740 then (if i < 738 then (if i < 737 then 9 else 8) else (if i < 739 then 9 else 10)) else (if i < 742 then (if i < 741 then 9 else 10) else (if i < 743 then 9 else 8))) else (if i < 748 then (if i < 746 then (if i < 745 then 8 else 9) else (if i < 747 then 10 else 9)) else (if i < 750 then (if i < 749 then 10 else 8) else (if i < 751 then 9 else 9)))) else (if i < 760 then (if i < 756 then (if i < 754 then (if i < 753 then 10 else 9) else (if i < 755 then 10 else 10)) else (if i < 758 then (if i < 757 then 10 else 10) else (if i < 759 then 9 else 10))) else (if i < 764 then (if i < 762 then (if i < 761 then 8 else 6) else (if i < 763 then 7 else 7)) else (if i < 766 then (if i < 765 then 8 else 9) else (if i < 767 then 10 else 8)))))

private def connectRankValue_b24 (i : ℕ) : ℕ :=
  (if i < 784 then (if i < 776 then (if i < 772 then (if i < 770 then (if i < 769 then 9 else 9) else (if i < 771 then 8 else 9)) else (if i < 774 then (if i < 773 then 7 else 9) else (if i < 775 then 9 else 10))) else (if i < 780 then (if i < 778 then (if i < 777 then 10 else 9) else (if i < 779 then 10 else 10)) else (if i < 782 then (if i < 781 then 10 else 9) else (if i < 783 then 10 else 10)))) else (if i < 792 then (if i < 788 then (if i < 786 then (if i < 785 then 9 else 9) else (if i < 787 then 8 else 8)) else (if i < 790 then (if i < 789 then 9 else 10) else (if i < 791 then 9 else 10))) else (if i < 796 then (if i < 794 then (if i < 793 then 8 else 7) else (if i < 795 then 6 else 5)) else (if i < 798 then (if i < 797 then 7 else 6) else (if i < 799 then 5 else 6)))))

private def connectRankValue_b25 (i : ℕ) : ℕ :=
  (if i < 816 then (if i < 808 then (if i < 804 then (if i < 802 then (if i < 801 then 6 else 7) else (if i < 803 then 7 else 5)) else (if i < 806 then (if i < 805 then 7 else 6) else (if i < 807 then 7 else 7))) else (if i < 812 then (if i < 810 then (if i < 809 then 7 else 6) else (if i < 811 then 6 else 7)) else (if i < 814 then (if i < 813 then 8 else 7) else (if i < 815 then 7 else 6)))) else (if i < 824 then (if i < 820 then (if i < 818 then (if i < 817 then 7 else 7) else (if i < 819 then 8 else 8)) else (if i < 822 then (if i < 821 then 8 else 8) else (if i < 823 then 8 else 9))) else (if i < 828 then (if i < 826 then (if i < 825 then 7 else 8) else (if i < 827 then 10 else 6)) else (if i < 830 then (if i < 829 then 7 else 8) else (if i < 831 then 10 else 9)))))

private def connectRankValue_b26 (i : ℕ) : ℕ :=
  (if i < 848 then (if i < 840 then (if i < 836 then (if i < 834 then (if i < 833 then 9 else 10) else (if i < 835 then 7 else 8)) else (if i < 838 then (if i < 837 then 8 else 9) else (if i < 839 then 9 else 8))) else (if i < 844 then (if i < 842 then (if i < 841 then 9 else 10) else (if i < 843 then 9 else 10)) else (if i < 846 then (if i < 845 then 9 else 8) else (if i < 847 then 8 else 9)))) else (if i < 856 then (if i < 852 then (if i < 850 then (if i < 849 then 10 else 9) else (if i < 851 then 10 else 8)) else (if i < 854 then (if i < 853 then 9 else 9) else (if i < 855 then 10 else 9))) else (if i < 860 then (if i < 858 then (if i < 857 then 10 else 10) else (if i < 859 then 10 else 10)) else (if i < 862 then (if i < 861 then 9 else 10) else (if i < 863 then 8 else 6)))))

private def connectRankValue_b27 (i : ℕ) : ℕ :=
  (if i < 880 then (if i < 872 then (if i < 868 then (if i < 866 then (if i < 865 then 7 else 7) else (if i < 867 then 8 else 9)) else (if i < 870 then (if i < 869 then 10 else 8) else (if i < 871 then 9 else 9))) else (if i < 876 then (if i < 874 then (if i < 873 then 8 else 9) else (if i < 875 then 7 else 9)) else (if i < 878 then (if i < 877 then 9 else 10) else (if i < 879 then 10 else 9)))) else (if i < 888 then (if i < 884 then (if i < 882 then (if i < 881 then 10 else 10) else (if i < 883 then 10 else 9)) else (if i < 886 then (if i < 885 then 10 else 10) else (if i < 887 then 9 else 9))) else (if i < 892 then (if i < 890 then (if i < 889 then 8 else 8) else (if i < 891 then 9 else 10)) else (if i < 894 then (if i < 893 then 9 else 10) else (if i < 895 then 8 else 7)))))

private def connectRankValue_b28 (i : ℕ) : ℕ :=
  (if i < 912 then (if i < 904 then (if i < 900 then (if i < 898 then (if i < 897 then 6 else 5) else (if i < 899 then 7 else 6)) else (if i < 902 then (if i < 901 then 5 else 6) else (if i < 903 then 6 else 7))) else (if i < 908 then (if i < 906 then (if i < 905 then 7 else 5) else (if i < 907 then 7 else 6)) else (if i < 910 then (if i < 909 then 7 else 7) else (if i < 911 then 7 else 6)))) else (if i < 920 then (if i < 916 then (if i < 914 then (if i < 913 then 6 else 7) else (if i < 915 then 8 else 7)) else (if i < 918 then (if i < 917 then 7 else 6) else (if i < 919 then 7 else 7))) else (if i < 924 then (if i < 922 then (if i < 921 then 8 else 8) else (if i < 923 then 8 else 8)) else (if i < 926 then (if i < 925 then 8 else 9) else (if i < 927 then 7 else 8)))))

private def connectRankValue_b29 (i : ℕ) : ℕ :=
  (if i < 944 then (if i < 936 then (if i < 932 then (if i < 930 then (if i < 929 then 10 else 6) else (if i < 931 then 7 else 12)) else (if i < 934 then (if i < 933 then 10 else 9) else (if i < 935 then 11 else 10))) else (if i < 940 then (if i < 938 then (if i < 937 then 9 else 10) else (if i < 939 then 10 else 11)) else (if i < 942 then (if i < 941 then 11 else 9) else (if i < 943 then 11 else 10)))) else (if i < 952 then (if i < 948 then (if i < 946 then (if i < 945 then 11 else 11) else (if i < 947 then 11 else 10)) else (if i < 950 then (if i < 949 then 10 else 11) else (if i < 951 then 12 else 11))) else (if i < 956 then (if i < 954 then (if i < 953 then 11 else 10) else (if i < 955 then 11 else 11)) else (if i < 958 then (if i < 957 then 12 else 12) else (if i < 959 then 12 else 12)))))

private def connectRankValue_b30 (i : ℕ) : ℕ :=
  (if i < 976 then (if i < 968 then (if i < 964 then (if i < 962 then (if i < 961 then 12 else 13) else (if i < 963 then 11 else 12)) else (if i < 966 then (if i < 965 then 12 else 10) else (if i < 967 then 9 else 11))) else (if i < 972 then (if i < 970 then (if i < 969 then 10 else 9) else (if i < 971 then 10 else 10)) else (if i < 974 then (if i < 973 then 11 else 11) else (if i < 975 then 9 else 11)))) else (if i < 984 then (if i < 980 then (if i < 978 then (if i < 977 then 10 else 11) else (if i < 979 then 11 else 11)) else (if i < 982 then (if i < 981 then 10 else 10) else (if i < 983 then 11 else 12))) else (if i < 988 then (if i < 986 then (if i < 985 then 11 else 11) else (if i < 987 then 10 else 11)) else (if i < 990 then (if i < 989 then 11 else 12) else (if i < 991 then 12 else 12)))))

private def connectRankValue_b31 (i : ℕ) : ℕ :=
  (if i < 1008 then (if i < 1000 then (if i < 996 then (if i < 994 then (if i < 993 then 12 else 12) else (if i < 995 then 13 else 11)) else (if i < 998 then (if i < 997 then 12 else 11) else (if i < 999 then 10 else 9))) else (if i < 1004 then (if i < 1002 then (if i < 1001 then 11 else 10) else (if i < 1003 then 9 else 10)) else (if i < 1006 then (if i < 1005 then 10 else 11) else (if i < 1007 then 11 else 9)))) else (if i < 1016 then (if i < 1012 then (if i < 1010 then (if i < 1009 then 11 else 10) else (if i < 1011 then 11 else 11)) else (if i < 1014 then (if i < 1013 then 11 else 10) else (if i < 1015 then 10 else 11))) else (if i < 1020 then (if i < 1018 then (if i < 1017 then 12 else 11) else (if i < 1019 then 11 else 10)) else (if i < 1022 then (if i < 1021 then 11 else 11) else (if i < 1023 then 12 else 12)))))

private def connectRankValue_b32 (i : ℕ) : ℕ :=
  (if i < 1040 then (if i < 1032 then (if i < 1028 then (if i < 1026 then (if i < 1025 then 12 else 12) else (if i < 1027 then 12 else 13)) else (if i < 1030 then (if i < 1029 then 11 else 12) else (if i < 1031 then 10 else 10))) else (if i < 1036 then (if i < 1034 then (if i < 1033 then 10 else 2) else (if i < 1035 then 1 else 5)) else (if i < 1038 then (if i < 1037 then 4 else 5) else (if i < 1039 then 6 else 2)))) else (if i < 1048 then (if i < 1044 then (if i < 1042 then (if i < 1041 then 3 else 2) else (if i < 1043 then 2 else 5)) else (if i < 1046 then (if i < 1045 then 6 else 6) else (if i < 1047 then 3 else 2))) else (if i < 1052 then (if i < 1050 then (if i < 1049 then 6 else 8) else (if i < 1051 then 6 else 6)) else (if i < 1054 then (if i < 1053 then 6 else 10) else (if i < 1055 then 3 else 1)))))

private def connectRankValue_b33 (i : ℕ) : ℕ :=
  (if i < 1057 then 2 else 4)

private def connectRankValue_n0_0 (i : ℕ) : ℕ := if i < 32 then connectRankValue_b0 i else connectRankValue_b1 i

private def connectRankValue_n0_1 (i : ℕ) : ℕ := if i < 96 then connectRankValue_b2 i else connectRankValue_b3 i

private def connectRankValue_n0_2 (i : ℕ) : ℕ := if i < 160 then connectRankValue_b4 i else connectRankValue_b5 i

private def connectRankValue_n0_3 (i : ℕ) : ℕ := if i < 224 then connectRankValue_b6 i else connectRankValue_b7 i

private def connectRankValue_n0_4 (i : ℕ) : ℕ := if i < 288 then connectRankValue_b8 i else connectRankValue_b9 i

private def connectRankValue_n0_5 (i : ℕ) : ℕ := if i < 352 then connectRankValue_b10 i else connectRankValue_b11 i

private def connectRankValue_n0_6 (i : ℕ) : ℕ := if i < 416 then connectRankValue_b12 i else connectRankValue_b13 i

private def connectRankValue_n0_7 (i : ℕ) : ℕ := if i < 480 then connectRankValue_b14 i else connectRankValue_b15 i

private def connectRankValue_n0_8 (i : ℕ) : ℕ := if i < 544 then connectRankValue_b16 i else connectRankValue_b17 i

private def connectRankValue_n0_9 (i : ℕ) : ℕ := if i < 608 then connectRankValue_b18 i else connectRankValue_b19 i

private def connectRankValue_n0_10 (i : ℕ) : ℕ := if i < 672 then connectRankValue_b20 i else connectRankValue_b21 i

private def connectRankValue_n0_11 (i : ℕ) : ℕ := if i < 736 then connectRankValue_b22 i else connectRankValue_b23 i

private def connectRankValue_n0_12 (i : ℕ) : ℕ := if i < 800 then connectRankValue_b24 i else connectRankValue_b25 i

private def connectRankValue_n0_13 (i : ℕ) : ℕ := if i < 864 then connectRankValue_b26 i else connectRankValue_b27 i

private def connectRankValue_n0_14 (i : ℕ) : ℕ := if i < 928 then connectRankValue_b28 i else connectRankValue_b29 i

private def connectRankValue_n0_15 (i : ℕ) : ℕ := if i < 992 then connectRankValue_b30 i else connectRankValue_b31 i

private def connectRankValue_n0_16 (i : ℕ) : ℕ := if i < 1056 then connectRankValue_b32 i else connectRankValue_b33 i

private def connectRankValue_n1_0 (i : ℕ) : ℕ := if i < 64 then connectRankValue_n0_0 i else connectRankValue_n0_1 i

private def connectRankValue_n1_1 (i : ℕ) : ℕ := if i < 192 then connectRankValue_n0_2 i else connectRankValue_n0_3 i

private def connectRankValue_n1_2 (i : ℕ) : ℕ := if i < 320 then connectRankValue_n0_4 i else connectRankValue_n0_5 i

private def connectRankValue_n1_3 (i : ℕ) : ℕ := if i < 448 then connectRankValue_n0_6 i else connectRankValue_n0_7 i

private def connectRankValue_n1_4 (i : ℕ) : ℕ := if i < 576 then connectRankValue_n0_8 i else connectRankValue_n0_9 i

private def connectRankValue_n1_5 (i : ℕ) : ℕ := if i < 704 then connectRankValue_n0_10 i else connectRankValue_n0_11 i

private def connectRankValue_n1_6 (i : ℕ) : ℕ := if i < 832 then connectRankValue_n0_12 i else connectRankValue_n0_13 i

private def connectRankValue_n1_7 (i : ℕ) : ℕ := if i < 960 then connectRankValue_n0_14 i else connectRankValue_n0_15 i

private def connectRankValue_n2_0 (i : ℕ) : ℕ := if i < 128 then connectRankValue_n1_0 i else connectRankValue_n1_1 i

private def connectRankValue_n2_1 (i : ℕ) : ℕ := if i < 384 then connectRankValue_n1_2 i else connectRankValue_n1_3 i

private def connectRankValue_n2_2 (i : ℕ) : ℕ := if i < 640 then connectRankValue_n1_4 i else connectRankValue_n1_5 i

private def connectRankValue_n2_3 (i : ℕ) : ℕ := if i < 896 then connectRankValue_n1_6 i else connectRankValue_n1_7 i

private def connectRankValue_n3_0 (i : ℕ) : ℕ := if i < 256 then connectRankValue_n2_0 i else connectRankValue_n2_1 i

private def connectRankValue_n3_1 (i : ℕ) : ℕ := if i < 768 then connectRankValue_n2_2 i else connectRankValue_n2_3 i

private def connectRankValue_n4_0 (i : ℕ) : ℕ := if i < 512 then connectRankValue_n3_0 i else connectRankValue_n3_1 i

private def connectRankValue_n5_0 (i : ℕ) : ℕ := if i < 1024 then connectRankValue_n4_0 i else connectRankValue_n0_16 i

def connectRankValue (i : ℕ) : ℕ := connectRankValue_n5_0 i

end PlanarHom.ColoringMacroFaces.FanFramed
