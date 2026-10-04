import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.WireFramed
private def vertexRankValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 1 else 5) else (if i < 3 then 3 else 0)) else (if i < 6 then (if i < 5 then 3 else 10) else (if i < 7 then 8 else 3))) else (if i < 12 then (if i < 10 then (if i < 9 then 2 else 0) else (if i < 11 then 4 else 1)) else (if i < 14 then (if i < 13 then 4 else 2) else (if i < 15 then 9 else 3)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0 else 4) else (if i < 19 then 2 else 4)) else (if i < 22 then (if i < 21 then 2 else 6) else (if i < 23 then 4 else 2))) else (if i < 28 then (if i < 26 then (if i < 25 then 1 else 3) else (if i < 27 then 3 else 0)) else (if i < 30 then (if i < 29 then 3 else 1) else (if i < 31 then 5 else 2)))))

private def vertexRankValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 3 else 7) else (if i < 35 then 5 else 1)) else (if i < 38 then (if i < 37 then 8 else 2) else (if i < 39 then 0 else 5))) else (if i < 44 then (if i < 42 then (if i < 41 then 4 else 0) else (if i < 43 then 6 else 1)) else (if i < 46 then (if i < 45 then 0 else 2) else (if i < 47 then 1 else 3)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0 else 3) else (if i < 51 then 1 else 7)) else (if i < 54 then (if i < 53 then 5 else 1) else (if i < 55 then 5 else 2))) else (if i < 60 then (if i < 58 then (if i < 57 then 1 else 3) else (if i < 59 then 2 else 0)) else (if i < 62 then (if i < 61 then 6 else 1) else (if i < 63 then 0 else 2)))))

private def vertexRankValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0 else 4) else (if i < 67 then 2 else 0)) else (if i < 70 then (if i < 69 then 2 else 0) else (if i < 71 then 2 else 2))) else (if i < 76 then (if i < 74 then (if i < 73 then 1 else 3) else (if i < 75 then 3 else 0)) else (if i < 78 then (if i < 77 then 3 else 1) else (if i < 79 then 3 else 2)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 1 else 0) else (if i < 83 then 2 else 5)) else (if i < 86 then (if i < 85 then 3 else 0) else (if i < 87 then 1 else 4))) else (if i < 92 then (if i < 90 then (if i < 89 then 2 else 0) else (if i < 91 then 3 else 1)) else (if i < 94 then (if i < 93 then 1 else 0) else (if i < 95 then 2 else 1)))))

private def vertexRankValue_b3 (i : ℕ) : ℕ :=
  (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 1 else 3) else (if i < 99 then 2 else 4)) else (if i < 102 then (if i < 101 then 3 else 0) else (if i < 103 then 2 else 7))) else (if i < 108 then (if i < 106 then (if i < 105 then 0 else 2) else (if i < 107 then 4 else 1)) else (if i < 110 then (if i < 109 then 2 else 3) else (if i < 111 then 1 else 2)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 8 else 1) else (if i < 115 then 3 else 0)) else (if i < 118 then (if i < 117 then 4 else 5) else (if i < 119 then 1 else 3))) else (if i < 124 then (if i < 122 then (if i < 121 then 1 else 2) else (if i < 123 then 0 else 2)) else (if i < 126 then (if i < 125 then 3 else 0) else (if i < 127 then 0 else 3)))))

private def vertexRankValue_b4 (i : ℕ) : ℕ :=
  (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 0 else 2) else (if i < 131 then 3 else 1)) else (if i < 134 then (if i < 133 then 1 else 3) else (if i < 135 then 0 else 4))) else (if i < 140 then (if i < 138 then (if i < 137 then 0 else 2) else (if i < 139 then 1 else 5)) else (if i < 142 then (if i < 141 then 0 else 3) else (if i < 143 then 0 else 1)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 2 else 2) else (if i < 147 then 0 else 2)) else (if i < 150 then (if i < 149 then 1 else 4) else (if i < 151 then 1 else 3))) else (if i < 156 then (if i < 154 then (if i < 153 then 1 else 0) else (if i < 155 then 4 else 1)) else (if i < 158 then (if i < 157 then 4 else 2) else (if i < 159 then 0 else 3)))))

private def vertexRankValue_b5 (i : ℕ) : ℕ :=
  (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 2 else 0) else (if i < 163 then 5 else 1)) else (if i < 166 then (if i < 165 then 0 else 2) else (if i < 167 then 1 else 3))) else (if i < 172 then (if i < 170 then (if i < 169 then 2 else 5) else (if i < 171 then 3 else 1)) else (if i < 174 then (if i < 173 then 4 else 2) else (if i < 175 then 0 else 4)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 3 else 0) else (if i < 179 then 4 else 1)) else (if i < 182 then (if i < 181 then 0 else 2) else (if i < 183 then 1 else 3))) else (if i < 188 then (if i < 186 then (if i < 185 then 5 else 1) else (if i < 187 then 7 else 2)) else (if i < 190 then (if i < 189 then 0 else 3) else (if i < 191 then 1 else 0)))))

private def vertexRankValue_b6 (i : ℕ) : ℕ :=
  (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 6 else 1) else (if i < 195 then 0 else 2)) else (if i < 198 then (if i < 197 then 1 else 3) else (if i < 199 then 2 else 0))) else (if i < 204 then (if i < 202 then (if i < 201 then 1 else 3) else (if i < 203 then 1 else 8)) else (if i < 206 then (if i < 205 then 6 else 3) else (if i < 207 then 1 else 3)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 2 else 0) else (if i < 211 then 2 else 1)) else (if i < 214 then (if i < 213 then 7 else 2) else (if i < 215 then 2 else 3))) else (if i < 220 then (if i < 218 then (if i < 217 then 3 else 0) else (if i < 219 then 4 else 1)) else (if i < 222 then (if i < 221 then 3 else 0) else (if i < 223 then 2 else 5)))))

private def vertexRankValue_b7 (i : ℕ) : ℕ :=
  (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 4 else 0) else (if i < 227 then 5 else 1)) else (if i < 230 then (if i < 229 then 0 else 2) else (if i < 231 then 3 else 3))) else (if i < 236 then (if i < 234 then (if i < 233 then 2 else 0) else (if i < 235 then 3 else 1)) else (if i < 238 then (if i < 237 then 0 else 1) else (if i < 239 then 2 else 0)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 0 else 2) else (if i < 243 then 5 else 1)) else (if i < 246 then (if i < 245 then 3 else 0) else (if i < 247 then 2 else 2))) else (if i < 252 then (if i < 250 then (if i < 249 then 1 else 0) else (if i < 251 then 4 else 1)) else (if i < 254 then (if i < 253 then 0 else 2) else (if i < 255 then 0 else 3)))))

private def vertexRankValue_b8 (i : ℕ) : ℕ :=
  (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 5 else 4) else (if i < 259 then 0 else 2)) else (if i < 262 then (if i < 261 then 3 else 1) else (if i < 263 then 3 else 0))) else (if i < 268 then (if i < 266 then (if i < 265 then 4 else 3) else (if i < 267 then 5 else 2)) else (if i < 270 then (if i < 269 then 6 else 1) else (if i < 271 then 3 else 0)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 2 else 3) else (if i < 275 then 1 else 4)) else (if i < 278 then (if i < 277 then 5 else 1) else (if i < 279 then 2 else 0))) else (if i < 284 then (if i < 282 then (if i < 281 then 1 else 3) else (if i < 283 then 0 else 2)) else (if i < 286 then (if i < 285 then 3 else 1) else (if i < 287 then 2 else 0)))))

private def vertexRankValue_b9 (i : ℕ) : ℕ :=
  (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 1 else 0) else (if i < 291 then 2 else 1)) else (if i < 294 then (if i < 293 then 1 else 5) else (if i < 295 then 2 else 2))) else (if i < 300 then (if i < 298 then (if i < 297 then 4 else 0) else (if i < 299 then 1 else 3)) else (if i < 302 then (if i < 301 then 2 else 1) else (if i < 303 then 3 else 0)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 2 else 3) else (if i < 307 then 1 else 4)) else (if i < 310 then (if i < 309 then 2 else 4) else (if i < 311 then 2 else 4))) else (if i < 316 then (if i < 314 then (if i < 313 then 3 else 1) else (if i < 315 then 2 else 2)) else (if i < 318 then (if i < 317 then 3 else 3) else (if i < 319 then 3 else 0)))))

private def vertexRankValue_b10 (i : ℕ) : ℕ :=
  (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 3 else 1) else (if i < 323 then 8 else 4)) else (if i < 326 then (if i < 325 then 2 else 5) else (if i < 327 then 3 else 0))) else (if i < 332 then (if i < 330 then (if i < 329 then 4 else 1) else (if i < 331 then 0 else 2)) else (if i < 334 then (if i < 333 then 3 else 3) else (if i < 335 then 4 else 0)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 2 else 5) else (if i < 339 then 3 else 7)) else (if i < 342 then (if i < 341 then 5 else 0) else (if i < 343 then 4 else 4))) else (if i < 348 then (if i < 346 then (if i < 345 then 3 else 3) else (if i < 347 then 4 else 0)) else (if i < 350 then (if i < 349 then 6 else 1) else (if i < 351 then 5 else 2)))))

private def vertexRankValue_b11 (i : ℕ) : ℕ :=
  (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 2 else 1) else (if i < 355 then 3 else 4)) else (if i < 358 then (if i < 357 then 2 else 5) else (if i < 359 then 3 else 0))) else (if i < 364 then (if i < 362 then (if i < 361 then 3 else 2) else (if i < 363 then 0 else 3)) else (if i < 366 then (if i < 365 then 3 else 0) else (if i < 367 then 4 else 1)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 5 else 2) else (if i < 371 then 0 else 2)) else (if i < 374 then (if i < 373 then 0 else 3) else (if i < 375 then 1 else 7))) else (if i < 380 then (if i < 378 then (if i < 377 then 6 else 1) else (if i < 379 then 1 else 2)) else (if i < 382 then (if i < 381 then 1 else 3) else (if i < 383 then 2 else 0)))))

private def vertexRankValue_b12 (i : ℕ) : ℕ :=
  (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 0 else 2) else (if i < 387 then 1 else 3)) else (if i < 390 then (if i < 389 then 1 else 2) else (if i < 391 then 0 else 2))) else (if i < 396 then (if i < 394 then (if i < 393 then 1 else 4) else (if i < 395 then 1 else 0)) else (if i < 398 then (if i < 397 then 5 else 2) else (if i < 399 then 1 else 3)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 0 else 1) else (if i < 403 then 0 else 2)) else (if i < 406 then (if i < 405 then 2 else 3) else (if i < 407 then 1 else 6))) else (if i < 412 then (if i < 410 then (if i < 409 then 8 else 1) else (if i < 411 then 3 else 0)) else (if i < 414 then (if i < 413 then 1 else 3) else (if i < 415 then 0 else 2)))))

private def vertexRankValue_b13 (i : ℕ) : ℕ :=
  (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 7 else 1) else (if i < 419 then 2 else 0)) else (if i < 422 then (if i < 421 then 2 else 3) else (if i < 423 then 5 else 2))) else (if i < 428 then (if i < 426 then (if i < 425 then 0 else 2) else (if i < 427 then 0 else 0)) else (if i < 430 then (if i < 429 then 1 else 2) else (if i < 431 then 4 else 1)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 3 else 0) else (if i < 435 then 3 else 3)) else (if i < 438 then (if i < 437 then 1 else 2) else (if i < 439 then 0 else 2))) else (if i < 444 then (if i < 442 then (if i < 441 then 3 else 1) else (if i < 443 then 0 else 4)) else (if i < 446 then (if i < 445 then 2 else 1) else (if i < 447 then 5 else 1)))))

private def vertexRankValue_b14 (i : ℕ) : ℕ :=
  (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 0 else 2) else (if i < 451 then 0 else 1)) else (if i < 454 then (if i < 453 then 1 else 3) else (if i < 455 then 0 else 2))) else (if i < 460 then (if i < 458 then (if i < 457 then 0 else 6) else (if i < 459 then 8 else 6)) else (if i < 462 then (if i < 461 then 8 else 1) else (if i < 463 then 2 else 3)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 8 else 2) else (if i < 467 then 7 else 1)) else (if i < 470 then (if i < 469 then 7 else 0) else (if i < 471 then 3 else 0))) else (if i < 476 then (if i < 474 then (if i < 473 then 2 else 8) else (if i < 475 then 10 else 3)) else (if i < 478 then (if i < 477 then 4 else 0) else (if i < 479 then 2 else 3)))))

private def vertexRankValue_b15 (i : ℕ) : ℕ :=
  (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 1 else 2) else (if i < 483 then 9 else 1)) else (if i < 486 then (if i < 485 then 7 else 1) else (if i < 487 then 3 else 3))) else (if i < 492 then (if i < 490 then (if i < 489 then 5 else 0) else (if i < 491 then 1 else 2)) else (if i < 494 then (if i < 493 then 6 else 1) else (if i < 495 then 2 else 0)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 4 else 3) else (if i < 499 then 1 else 3)) else (if i < 502 then (if i < 501 then 2 else 0) else (if i < 503 then 4 else 2))) else (if i < 508 then (if i < 506 then (if i < 505 then 0 else 1) else (if i < 507 then 1 else 9)) else (if i < 510 then (if i < 509 then 10 else 3) else (if i < 511 then 1 else 3)))))

private def vertexRankValue_b16 (i : ℕ) : ℕ :=
  (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 1 else 5) else (if i < 515 then 3 else 0)) else (if i < 518 then (if i < 517 then 11 else 1) else (if i < 519 then 2 else 2))) else (if i < 524 then (if i < 522 then (if i < 521 then 2 else 3) else (if i < 523 then 4 else 0)) else (if i < 526 then (if i < 525 then 3 else 1) else (if i < 527 then 8 else 3)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 1 else 5) else (if i < 531 then 3 else 0)) else (if i < 534 then (if i < 533 then 4 else 1) else (if i < 535 then 0 else 2))) else (if i < 540 then (if i < 538 then (if i < 537 then 2 else 3) else (if i < 539 then 4 else 0)) else (if i < 542 then (if i < 541 then 0 else 7) else (if i < 543 then 5 else 7)))))

private def vertexRankValue_b17 (i : ℕ) : ℕ :=
  (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then 5 else 0) else (if i < 547 then 4 else 2)) else (if i < 550 then (if i < 549 then 1 else 3) else (if i < 551 then 6 else 0))) else (if i < 556 then (if i < 554 then (if i < 553 then 6 else 1) else (if i < 555 then 5 else 2)) else (if i < 558 then (if i < 557 then 2 else 1) else (if i < 559 then 3 else 4)))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then 2 else 5) else (if i < 563 then 3 else 0)) else (if i < 566 then (if i < 565 then 3 else 2) else (if i < 567 then 0 else 3))) else (if i < 572 then (if i < 570 then (if i < 569 then 3 else 0) else (if i < 571 then 4 else 1)) else (if i < 574 then (if i < 573 then 6 else 2) else (if i < 575 then 0 else 2)))))

private def vertexRankValue_b18 (i : ℕ) : ℕ :=
  (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then 0 else 3) else (if i < 579 then 1 else 8)) else (if i < 582 then (if i < 581 then 7 else 1) else (if i < 583 then 1 else 2))) else (if i < 588 then (if i < 586 then (if i < 585 then 1 else 3) else (if i < 587 then 2 else 0)) else (if i < 590 then (if i < 589 then 4 else 2) else (if i < 591 then 0 else 3)))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then 1 else 2) else (if i < 595 then 0 else 2)) else (if i < 598 then (if i < 597 then 1 else 4) else (if i < 599 then 1 else 0))) else (if i < 604 then (if i < 602 then (if i < 601 then 5 else 2) else (if i < 603 then 1 else 3)) else (if i < 606 then (if i < 605 then 0 else 1) else (if i < 607 then 0 else 2)))))

private def vertexRankValue_b19 (i : ℕ) : ℕ :=
  (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then 2 else 3) else (if i < 611 then 1 else 6)) else (if i < 614 then (if i < 613 then 8 else 1) else (if i < 615 then 3 else 0))) else (if i < 620 then (if i < 618 then (if i < 617 then 1 else 3) else (if i < 619 then 0 else 2)) else (if i < 622 then (if i < 621 then 7 else 1) else (if i < 623 then 2 else 0)))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then 4 else 3) else (if i < 627 then 5 else 2)) else (if i < 630 then (if i < 629 then 0 else 1) else (if i < 631 then 3 else 2))) else (if i < 636 then (if i < 634 then (if i < 633 then 3 else 3) else (if i < 635 then 4 else 2)) else (if i < 638 then (if i < 637 then 3 else 1) else (if i < 639 then 2 else 0)))))

private def vertexRankValue_b20 (i : ℕ) : ℕ :=
  (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then 0 else 2) else (if i < 643 then 4 else 2)) else (if i < 646 then (if i < 645 then 3 else 1) else (if i < 647 then 0 else 4))) else (if i < 652 then (if i < 650 then (if i < 649 then 2 else 1) else (if i < 651 then 5 else 1)) else (if i < 654 then (if i < 653 then 0 else 2) else (if i < 655 then 0 else 1)))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then 0 else 2) else (if i < 659 then 0 else 1)) else (if i < 662 then (if i < 661 then 1 else 5) else (if i < 663 then 3 else 0))) else (if i < 668 then (if i < 666 then (if i < 665 then 3 else 6) else (if i < 667 then 4 else 3)) else (if i < 670 then (if i < 669 then 2 else 0) else (if i < 671 then 4 else 1)))))

private def vertexRankValue_b21 (i : ℕ) : ℕ :=
  (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then 4 else 2) else (if i < 675 then 5 else 3)) else (if i < 678 then (if i < 677 then 0 else 4) else (if i < 679 then 2 else 0))) else (if i < 684 then (if i < 682 then (if i < 681 then 3 else 8) else (if i < 683 then 6 else 2)) else (if i < 686 then (if i < 685 then 1 else 3) else (if i < 687 then 3 else 0)))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then 4 else 1) else (if i < 691 then 7 else 2)) else (if i < 694 then (if i < 693 then 3 else 7) else (if i < 695 then 5 else 1))) else (if i < 700 then (if i < 698 then (if i < 697 then 8 else 2) else (if i < 699 then 0 else 5)) else (if i < 702 then (if i < 701 then 4 else 0) else (if i < 703 then 6 else 1)))))

private def vertexRankValue_b22 (i : ℕ) : ℕ :=
  (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then 0 else 2) else (if i < 707 then 1 else 3)) else (if i < 710 then (if i < 709 then 0 else 3) else (if i < 711 then 1 else 7))) else (if i < 716 then (if i < 714 then (if i < 713 then 5 else 0) else (if i < 715 then 4 else 2)) else (if i < 718 then (if i < 717 then 1 else 3) else (if i < 719 then 2 else 0)))) else (if i < 728 then (if i < 724 then (if i < 722 then (if i < 721 then 6 else 1) else (if i < 723 then 5 else 2)) else (if i < 726 then (if i < 725 then 7 else 4) else (if i < 727 then 2 else 3))) else (if i < 732 then (if i < 730 then (if i < 729 then 1 else 0) else (if i < 731 then 2 else 0)) else (if i < 734 then (if i < 733 then 8 else 2) else (if i < 735 then 3 else 3)))))

private def vertexRankValue_b23 (i : ℕ) : ℕ :=
  (if i < 752 then (if i < 744 then (if i < 740 then (if i < 738 then (if i < 737 then 2 else 0) else (if i < 739 then 3 else 1)) else (if i < 742 then (if i < 741 then 1 else 0) else (if i < 743 then 2 else 5))) else (if i < 748 then (if i < 746 then (if i < 745 then 3 else 0) else (if i < 747 then 1 else 3)) else (if i < 750 then (if i < 749 then 2 else 0) else (if i < 751 then 2 else 0)))) else (if i < 760 then (if i < 756 then (if i < 754 then (if i < 753 then 1 else 2) else (if i < 755 then 1 else 0)) else (if i < 758 then (if i < 757 then 1 else 3) else (if i < 759 then 1 else 4))) else (if i < 764 then (if i < 762 then (if i < 761 then 3 else 1) else (if i < 763 then 3 else 0)) else (if i < 766 then (if i < 765 then 2 else 2) else (if i < 767 then 4 else 1)))))

private def vertexRankValue_b24 (i : ℕ) : ℕ :=
  (if i < 784 then (if i < 776 then (if i < 772 then (if i < 770 then (if i < 769 then 2 else 0) else (if i < 771 then 2 else 3)) else (if i < 774 then (if i < 773 then 1 else 2) else (if i < 775 then 3 else 1))) else (if i < 780 then (if i < 778 then (if i < 777 then 4 else 0) else (if i < 779 then 2 else 2)) else (if i < 782 then (if i < 781 then 0 else 2) else (if i < 783 then 0 else 2)))) else (if i < 792 then (if i < 788 then (if i < 786 then (if i < 785 then 3 else 0) else (if i < 787 then 1 else 3)) else (if i < 790 then (if i < 789 then 3 else 2) else (if i < 791 then 3 else 1))) else (if i < 796 then (if i < 794 then (if i < 793 then 2 else 0) else (if i < 795 then 1 else 5)) else (if i < 798 then (if i < 797 then 0 else 2) else (if i < 799 then 1 else 5)))))

private def vertexRankValue_b25 (i : ℕ) : ℕ :=
  (if i < 816 then (if i < 808 then (if i < 804 then (if i < 802 then (if i < 801 then 0 else 4) else (if i < 803 then 0 else 1)) else (if i < 806 then (if i < 805 then 3 else 2) else (if i < 807 then 0 else 1))) else (if i < 812 then (if i < 810 then (if i < 809 then 1 else 0) else (if i < 811 then 1 else 3)) else (if i < 814 then (if i < 813 then 4 else 1) else (if i < 815 then 5 else 2)))) else (if i < 824 then (if i < 820 then (if i < 818 then (if i < 817 then 0 else 3) else (if i < 819 then 1 else 0)) else (if i < 822 then (if i < 821 then 5 else 1) else (if i < 823 then 0 else 2))) else (if i < 828 then (if i < 826 then (if i < 825 then 1 else 3) else (if i < 827 then 2 else 0)) else (if i < 830 then (if i < 829 then 2 else 7) else (if i < 831 then 5 else 1)))))

private def vertexRankValue_b26 (i : ℕ) : ℕ :=
  (if i < 848 then (if i < 840 then (if i < 836 then (if i < 834 then (if i < 833 then 4 else 3) else (if i < 835 then 1 else 4)) else (if i < 838 then (if i < 837 then 3 else 0) else (if i < 839 then 6 else 1))) else (if i < 844 then (if i < 842 then (if i < 841 then 0 else 2) else (if i < 843 then 2 else 3)) else (if i < 846 then (if i < 845 then 5 else 2) else (if i < 847 then 0 else 4)))) else (if i < 856 then (if i < 852 then (if i < 850 then (if i < 849 then 2 else 4) else (if i < 851 then 2 else 0)) else (if i < 854 then (if i < 853 then 6 else 2) else (if i < 855 then 1 else 3))) else (if i < 860 then (if i < 858 then (if i < 857 then 3 else 0) else (if i < 859 then 3 else 1)) else (if i < 862 then (if i < 861 then 1 else 3) else (if i < 863 then 1 else 1)))))

private def vertexRankValue_b27 (i : ℕ) : ℕ :=
  (if i < 880 then (if i < 872 then (if i < 868 then (if i < 866 then (if i < 865 then 8 else 4) else (if i < 867 then 2 else 3)) else (if i < 870 then (if i < 869 then 2 else 0) else (if i < 871 then 2 else 1))) else (if i < 876 then (if i < 874 then (if i < 873 then 0 else 2) else (if i < 875 then 3 else 3)) else (if i < 878 then (if i < 877 then 4 else 0) else (if i < 879 then 4 else 1)))) else (if i < 888 then (if i < 884 then (if i < 882 then (if i < 881 then 3 else 1) else (if i < 883 then 3 else 6)) else (if i < 886 then (if i < 885 then 5 else 0) else (if i < 887 then 5 else 1))) else (if i < 892 then (if i < 890 then (if i < 889 then 0 else 2) else (if i < 891 then 0 else 3)) else (if i < 894 then (if i < 893 then 3 else 0) else (if i < 895 then 4 else 1)))))

private def vertexRankValue_b28 (i : ℕ) : ℕ :=
  (if i < 912 then (if i < 904 then (if i < 900 then (if i < 898 then (if i < 897 then 0 else 1) else (if i < 899 then 2 else 1)) else (if i < 902 then (if i < 901 then 0 else 2) else (if i < 903 then 0 else 1))) else (if i < 908 then (if i < 906 then (if i < 905 then 3 else 0) else (if i < 907 then 2 else 2)) else (if i < 910 then (if i < 909 then 2 else 0) else (if i < 911 then 5 else 1)))) else (if i < 920 then (if i < 916 then (if i < 914 then (if i < 913 then 0 else 2) else (if i < 915 then 0 else 4)) else (if i < 918 then (if i < 917 then 6 else 4) else (if i < 919 then 0 else 2))) else (if i < 924 then (if i < 922 then (if i < 921 then 3 else 2) else (if i < 923 then 3 else 1)) else (if i < 926 then (if i < 925 then 5 else 0) else (if i < 927 then 5 else 3)))))

private def vertexRankValue_b29 (i : ℕ) : ℕ :=
  (if i < 944 then (if i < 936 then (if i < 932 then (if i < 930 then (if i < 929 then 7 else 1) else (if i < 931 then 3 else 0)) else (if i < 934 then (if i < 933 then 2 else 3) else (if i < 935 then 1 else 5))) else (if i < 940 then (if i < 938 then (if i < 937 then 6 else 1) else (if i < 939 then 2 else 0)) else (if i < 942 then (if i < 941 then 1 else 3) else (if i < 943 then 0 else 2)))) else (if i < 952 then (if i < 948 then (if i < 946 then (if i < 945 then 3 else 1) else (if i < 947 then 2 else 0)) else (if i < 950 then (if i < 949 then 1 else 0) else (if i < 951 then 2 else 1))) else (if i < 956 then (if i < 954 then (if i < 953 then 1 else 5) else (if i < 955 then 2 else 0)) else (if i < 958 then (if i < 957 then 4 else 1) else (if i < 959 then 2 else 3)))))

private def vertexRankValue_b30 (i : ℕ) : ℕ :=
  (if i < 976 then (if i < 968 then (if i < 964 then (if i < 962 then (if i < 961 then 2 else 1) else (if i < 963 then 3 else 0)) else (if i < 966 then (if i < 965 then 0 else 3) else (if i < 967 then 5 else 1))) else (if i < 972 then (if i < 970 then (if i < 969 then 3 else 3) else (if i < 971 then 4 else 2)) else (if i < 974 then (if i < 973 then 8 else 1) else (if i < 975 then 4 else 0)))) else (if i < 984 then (if i < 980 then (if i < 978 then (if i < 977 then 2 else 3) else (if i < 979 then 1 else 8)) else (if i < 982 then (if i < 981 then 0 else 7) else (if i < 983 then 9 else 1))) else (if i < 988 then (if i < 986 then (if i < 985 then 2 else 0) else (if i < 987 then 0 else 3)) else (if i < 990 then (if i < 989 then 9 else 2) else (if i < 991 then 8 else 1)))))

private def vertexRankValue_b31 (i : ℕ) : ℕ :=
  (if i < 1008 then (if i < 1000 then (if i < 996 then (if i < 994 then (if i < 993 then 4 else 0) else (if i < 995 then 2 else 9)) else (if i < 998 then (if i < 997 then 0 else 3) else (if i < 999 then 4 else 1))) else (if i < 1004 then (if i < 1002 then (if i < 1001 then 3 else 0) else (if i < 1003 then 1 else 3)) else (if i < 1006 then (if i < 1005 then 10 else 2) else (if i < 1007 then 4 else 2)))) else (if i < 1016 then (if i < 1012 then (if i < 1010 then (if i < 1009 then 1 else 3) else (if i < 1011 then 2 else 0)) else (if i < 1014 then (if i < 1013 then 3 else 1) else (if i < 1015 then 4 else 7))) else (if i < 1020 then (if i < 1018 then (if i < 1017 then 4 else 0) else (if i < 1019 then 4 else 1)) else (if i < 1022 then (if i < 1021 then 4 else 2) else (if i < 1023 then 0 else 0)))))

private def vertexRankValue_b32 (i : ℕ) : ℕ :=
  (if i < 1040 then (if i < 1032 then (if i < 1028 then (if i < 1026 then (if i < 1025 then 5 else 0) else (if i < 1027 then 5 else 1)) else (if i < 1030 then (if i < 1029 then 0 else 2) else (if i < 1031 then 1 else 3))) else (if i < 1036 then (if i < 1034 then (if i < 1033 then 1 else 4) else (if i < 1035 then 2 else 0)) else (if i < 1038 then (if i < 1037 then 3 else 7) else (if i < 1039 then 5 else 3)))) else (if i < 1048 then (if i < 1044 then (if i < 1042 then (if i < 1041 then 2 else 3) else (if i < 1043 then 3 else 0)) else (if i < 1046 then (if i < 1045 then 4 else 1) else (if i < 1047 then 6 else 2))) else (if i < 1052 then (if i < 1050 then (if i < 1049 then 3 else 8) else (if i < 1051 then 6 else 1)) else (if i < 1054 then (if i < 1053 then 8 else 3) else (if i < 1055 then 1 else 5)))))

private def vertexRankValue_b33 (i : ℕ) : ℕ :=
  (if i < 1072 then (if i < 1064 then (if i < 1060 then (if i < 1058 then (if i < 1057 then 4 else 0) else (if i < 1059 then 7 else 1)) else (if i < 1062 then (if i < 1061 then 0 else 2) else (if i < 1063 then 2 else 3))) else (if i < 1068 then (if i < 1066 then (if i < 1065 then 1 else 3) else (if i < 1067 then 1 else 7)) else (if i < 1070 then (if i < 1069 then 5 else 2) else (if i < 1071 then 0 else 3)))) else (if i < 1080 then (if i < 1076 then (if i < 1074 then (if i < 1073 then 2 else 3) else (if i < 1075 then 2 else 0)) else (if i < 1078 then (if i < 1077 then 6 else 1) else (if i < 1079 then 1 else 2))) else (if i < 1084 then (if i < 1082 then (if i < 1081 then 3 else 5) else (if i < 1083 then 3 else 0)) else (if i < 1086 then (if i < 1085 then 2 else 0) else (if i < 1087 then 2 else 5)))))

private def vertexRankValue_b34 (i : ℕ) : ℕ :=
  (if i < 1104 then (if i < 1096 then (if i < 1092 then (if i < 1090 then (if i < 1089 then 4 else 0) else (if i < 1091 then 4 else 1)) else (if i < 1094 then (if i < 1093 then 3 else 2) else (if i < 1095 then 3 else 3))) else (if i < 1100 then (if i < 1098 then (if i < 1097 then 2 else 0) else (if i < 1099 then 3 else 0)) else (if i < 1102 then (if i < 1101 then 0 else 1) else (if i < 1103 then 2 else 5)))) else (if i < 1112 then (if i < 1108 then (if i < 1106 then (if i < 1105 then 0 else 1) else (if i < 1107 then 4 else 1)) else (if i < 1110 then (if i < 1109 then 2 else 0) else (if i < 1111 then 2 else 1))) else (if i < 1116 then (if i < 1114 then (if i < 1113 then 1 else 4) else (if i < 1115 then 3 else 0)) else (if i < 1118 then (if i < 1117 then 3 else 1) else (if i < 1119 then 3 else 8)))))

private def vertexRankValue_b35 (i : ℕ) : ℕ :=
  (if i < 1136 then (if i < 1128 then (if i < 1124 then (if i < 1122 then (if i < 1121 then 1 else 2) else (if i < 1123 then 4 else 1)) else (if i < 1126 then (if i < 1125 then 2 else 0) else (if i < 1127 then 2 else 3))) else (if i < 1132 then (if i < 1130 then (if i < 1129 then 0 else 2) else (if i < 1131 then 3 else 1)) else (if i < 1134 then (if i < 1133 then 5 else 1) else (if i < 1135 then 3 else 0)))) else (if i < 1144 then (if i < 1140 then (if i < 1138 then (if i < 1137 then 2 else 2) else (if i < 1139 then 0 else 3)) else (if i < 1142 then (if i < 1141 then 4 else 1) else (if i < 1143 then 2 else 0))) else (if i < 1148 then (if i < 1146 then (if i < 1145 then 1 else 3) else (if i < 1147 then 3 else 2)) else (if i < 1150 then (if i < 1149 then 2 else 0) else (if i < 1151 then 1 else 0)))))

private def vertexRankValue_b36 (i : ℕ) : ℕ :=
  (if i < 1168 then (if i < 1160 then (if i < 1156 then (if i < 1154 then (if i < 1153 then 0 else 2) else (if i < 1155 then 1 else 5)) else (if i < 1158 then (if i < 1157 then 0 else 5) else (if i < 1159 then 0 else 2))) else (if i < 1164 then (if i < 1162 then (if i < 1161 then 4 else 0) else (if i < 1163 then 1 else 3)) else (if i < 1166 then (if i < 1165 then 1 else 4) else (if i < 1167 then 1 else 3)))) else (if i < 1176 then (if i < 1172 then (if i < 1170 then (if i < 1169 then 1 else 0) else (if i < 1171 then 4 else 1)) else (if i < 1174 then (if i < 1173 then 4 else 1) else (if i < 1175 then 10 else 3))) else (if i < 1180 then (if i < 1178 then (if i < 1177 then 2 else 0) else (if i < 1179 then 5 else 1)) else (if i < 1182 then (if i < 1181 then 0 else 2) else (if i < 1183 then 0 else 3)))))

private def vertexRankValue_b37 (i : ℕ) : ℕ :=
  (if i < 1200 then (if i < 1192 then (if i < 1188 then (if i < 1186 then (if i < 1185 then 1 else 5) else (if i < 1187 then 3 else 1)) else (if i < 1190 then (if i < 1189 then 4 else 2) else (if i < 1191 then 0 else 3))) else (if i < 1196 then (if i < 1194 then (if i < 1193 then 2 else 0) else (if i < 1195 then 4 else 1)) else (if i < 1198 then (if i < 1197 then 0 else 2) else (if i < 1199 then 1 else 3)))) else (if i < 1208 then (if i < 1204 then (if i < 1202 then (if i < 1201 then 5 else 1) else (if i < 1203 then 7 else 2)) else (if i < 1206 then (if i < 1205 then 0 else 3) else (if i < 1207 then 1 else 0))) else (if i < 1212 then (if i < 1210 then (if i < 1209 then 6 else 1) else (if i < 1211 then 0 else 2)) else (if i < 1214 then (if i < 1213 then 1 else 3) else (if i < 1215 then 2 else 0)))))

private def vertexRankValue_b38 (i : ℕ) : ℕ :=
  (if i < 1232 then (if i < 1224 then (if i < 1220 then (if i < 1218 then (if i < 1217 then 1 else 3) else (if i < 1219 then 1 else 8)) else (if i < 1222 then (if i < 1221 then 6 else 2) else (if i < 1223 then 0 else 3))) else (if i < 1228 then (if i < 1226 then (if i < 1225 then 2 else 3) else (if i < 1227 then 2 else 0)) else (if i < 1230 then (if i < 1229 then 7 else 1) else (if i < 1231 then 1 else 2)))) else (if i < 1240 then (if i < 1236 then (if i < 1234 then (if i < 1233 then 2 else 5) else (if i < 1235 then 3 else 0)) else (if i < 1238 then (if i < 1237 then 2 else 0) else (if i < 1239 then 2 else 4))) else (if i < 1244 then (if i < 1242 then (if i < 1241 then 3 else 0) else (if i < 1243 then 4 else 1)) else (if i < 1246 then (if i < 1245 then 3 else 2) else (if i < 1247 then 3 else 3)))))

private def vertexRankValue_b39 (i : ℕ) : ℕ :=
  (if i < 1264 then (if i < 1256 then (if i < 1252 then (if i < 1250 then (if i < 1249 then 2 else 0) else (if i < 1251 then 3 else 0)) else (if i < 1254 then (if i < 1253 then 0 else 1) else (if i < 1255 then 2 else 5))) else (if i < 1260 then (if i < 1258 then (if i < 1257 then 0 else 1) else (if i < 1259 then 4 else 1)) else (if i < 1262 then (if i < 1261 then 2 else 0) else (if i < 1263 then 2 else 1)))) else (if i < 1272 then (if i < 1268 then (if i < 1266 then (if i < 1265 then 1 else 4) else (if i < 1267 then 3 else 0)) else (if i < 1270 then (if i < 1269 then 0 else 2) else (if i < 1271 then 0 else 3))) else (if i < 1276 then (if i < 1274 then (if i < 1273 then 5 else 4) else (if i < 1275 then 0 else 2)) else (if i < 1278 then (if i < 1277 then 3 else 1) else (if i < 1279 then 3 else 0)))))

private def vertexRankValue_b40 (i : ℕ) : ℕ :=
  (if i < 1296 then (if i < 1288 then (if i < 1284 then (if i < 1282 then (if i < 1281 then 4 else 3) else (if i < 1283 then 5 else 2)) else (if i < 1286 then (if i < 1285 then 6 else 1) else (if i < 1287 then 3 else 0))) else (if i < 1292 then (if i < 1290 then (if i < 1289 then 2 else 3) else (if i < 1291 then 1 else 4)) else (if i < 1294 then (if i < 1293 then 5 else 1) else (if i < 1295 then 2 else 0)))) else (if i < 1304 then (if i < 1300 then (if i < 1298 then (if i < 1297 then 1 else 3) else (if i < 1299 then 0 else 2)) else (if i < 1302 then (if i < 1301 then 3 else 1) else (if i < 1303 then 2 else 0))) else (if i < 1308 then (if i < 1306 then (if i < 1305 then 1 else 0) else (if i < 1307 then 2 else 1)) else (if i < 1310 then (if i < 1309 then 1 else 5) else (if i < 1311 then 2 else 0)))))

private def vertexRankValue_b41 (i : ℕ) : ℕ :=
  (if i < 1328 then (if i < 1320 then (if i < 1316 then (if i < 1314 then (if i < 1313 then 4 else 1) else (if i < 1315 then 2 else 3)) else (if i < 1318 then (if i < 1317 then 2 else 1) else (if i < 1319 then 3 else 0))) else (if i < 1324 then (if i < 1322 then (if i < 1321 then 7 else 5) else (if i < 1323 then 3 else 4)) else (if i < 1326 then (if i < 1325 then 2 else 5) else (if i < 1327 then 3 else 9)))) else (if i < 1336 then (if i < 1332 then (if i < 1330 then (if i < 1329 then 8 else 3) else (if i < 1331 then 4 else 0)) else (if i < 1334 then (if i < 1333 then 3 else 1) else (if i < 1335 then 4 else 2))) else (if i < 1340 then (if i < 1338 then (if i < 1337 then 3 else 3) else (if i < 1339 then 1 else 4)) else (if i < 1342 then (if i < 1341 then 2 else 5) else (if i < 1343 then 3 else 0)))))

private def vertexRankValue_b42 (i : ℕ) : ℕ :=
  (if i < 1360 then (if i < 1352 then (if i < 1348 then (if i < 1346 then (if i < 1345 then 4 else 2) else (if i < 1347 then 2 else 3)) else (if i < 1350 then (if i < 1349 then 3 else 0) else (if i < 1351 then 4 else 1))) else (if i < 1356 then (if i < 1354 then (if i < 1353 then 3 else 6) else (if i < 1355 then 4 else 0)) else (if i < 1358 then (if i < 1357 then 7 else 2) else (if i < 1359 then 0 else 5)))) else (if i < 1368 then (if i < 1364 then (if i < 1362 then (if i < 1361 then 4 else 0) else (if i < 1363 then 5 else 1)) else (if i < 1366 then (if i < 1365 then 8 else 2) else (if i < 1367 then 1 else 3))) else (if i < 1372 then (if i < 1370 then (if i < 1369 then 3 else 2) else (if i < 1371 then 0 else 6)) else (if i < 1374 then (if i < 1373 then 4 else 0) else (if i < 1375 then 4 else 1)))))

private def vertexRankValue_b43 (i : ℕ) : ℕ :=
  (if i < 1392 then (if i < 1384 then (if i < 1380 then (if i < 1378 then (if i < 1377 then 0 else 2) else (if i < 1379 then 1 else 3)) else (if i < 1382 then (if i < 1381 then 5 else 0) else (if i < 1383 then 5 else 1))) else (if i < 1388 then (if i < 1386 then (if i < 1385 then 6 else 3) else (if i < 1387 then 1 else 3)) else (if i < 1390 then (if i < 1389 then 1 else 3) else (if i < 1391 then 1 else 8)))) else (if i < 1400 then (if i < 1396 then (if i < 1394 then (if i < 1393 then 7 else 1) else (if i < 1395 then 2 else 2)) else (if i < 1398 then (if i < 1397 then 2 else 3) else (if i < 1399 then 2 else 0))) else (if i < 1404 then (if i < 1402 then (if i < 1401 then 0 else 3) else (if i < 1403 then 1 else 4)) else (if i < 1406 then (if i < 1405 then 2 else 0) else (if i < 1407 then 1 else 3)))))

private def vertexRankValue_b44 (i : ℕ) : ℕ :=
  (if i < 1424 then (if i < 1416 then (if i < 1412 then (if i < 1410 then (if i < 1409 then 2 else 5) else (if i < 1411 then 2 else 0)) else (if i < 1414 then (if i < 1413 then 0 else 2) else (if i < 1415 then 1 else 0))) else (if i < 1420 then (if i < 1418 then (if i < 1417 then 0 else 1) else (if i < 1419 then 1 else 2)) else (if i < 1422 then (if i < 1421 then 2 else 3) else (if i < 1423 then 1 else 6)))) else (if i < 1432 then (if i < 1428 then (if i < 1426 then (if i < 1425 then 8 else 1) else (if i < 1427 then 3 else 0)) else (if i < 1430 then (if i < 1429 then 1 else 3) else (if i < 1431 then 0 else 2))) else (if i < 1436 then (if i < 1434 then (if i < 1433 then 7 else 1) else (if i < 1435 then 2 else 0)) else (if i < 1438 then (if i < 1437 then 3 else 4) else (if i < 1439 then 0 else 2)))))

private def vertexRankValue_b45 (i : ℕ) : ℕ :=
  (if i < 1456 then (if i < 1448 then (if i < 1444 then (if i < 1442 then (if i < 1441 then 0 else 2) else (if i < 1443 then 0 else 1)) else (if i < 1446 then (if i < 1445 then 2 else 3) else (if i < 1447 then 5 else 2))) else (if i < 1452 then (if i < 1450 then (if i < 1449 then 3 else 1) else (if i < 1451 then 3 else 0)) else (if i < 1454 then (if i < 1453 then 1 else 2) else (if i < 1455 then 0 else 3)))) else (if i < 1464 then (if i < 1460 then (if i < 1458 then (if i < 1457 then 3 else 2) else (if i < 1459 then 1 else 4)) else (if i < 1462 then (if i < 1461 then 0 else 2) else (if i < 1463 then 5 else 1))) else (if i < 1468 then (if i < 1466 then (if i < 1465 then 1 else 2) else (if i < 1467 then 0 else 1)) else (if i < 1470 then (if i < 1469 then 1 else 4) else (if i < 1471 then 0 else 3)))))

private def vertexRankValue_b46 (i : ℕ) : ℕ :=
  (if i < 1488 then (if i < 1480 then (if i < 1476 then (if i < 1474 then (if i < 1473 then 1 else 6) else (if i < 1475 then 8 else 5)) else (if i < 1478 then (if i < 1477 then 7 else 1) else (if i < 1479 then 2 else 3))) else (if i < 1484 then (if i < 1482 then (if i < 1481 then 0 else 2) else (if i < 1483 then 7 else 1)) else (if i < 1486 then (if i < 1485 then 6 else 0) else (if i < 1487 then 3 else 0)))) else (if i < 1496 then (if i < 1492 then (if i < 1490 then (if i < 1489 then 2 else 9) else (if i < 1491 then 0 else 3)) else (if i < 1494 then (if i < 1493 then 4 else 1) else (if i < 1495 then 2 else 0))) else (if i < 1500 then (if i < 1498 then (if i < 1497 then 1 else 3) else (if i < 1499 then 10 else 2)) else (if i < 1502 then (if i < 1501 then 0 else 2) else (if i < 1503 then 4 else 6)))))

private def vertexRankValue_b47 (i : ℕ) : ℕ :=
  (if i < 1520 then (if i < 1512 then (if i < 1508 then (if i < 1506 then (if i < 1505 then 8 else 1) else (if i < 1507 then 2 else 3)) else (if i < 1510 then (if i < 1509 then 7 else 2) else (if i < 1511 then 3 else 1))) else (if i < 1516 then (if i < 1514 then (if i < 1513 then 7 else 0) else (if i < 1515 then 1 else 3)) else (if i < 1518 then (if i < 1517 then 2 else 1) else (if i < 1519 then 0 else 2)))) else (if i < 1528 then (if i < 1524 then (if i < 1522 then (if i < 1521 then 0 else 2) else (if i < 1523 then 2 else 9)) else (if i < 1526 then (if i < 1525 then 7 else 1) else (if i < 1527 then 5 else 2))) else (if i < 1532 then (if i < 1530 then (if i < 1529 then 0 else 3) else (if i < 1531 then 1 else 0)) else (if i < 1534 then (if i < 1533 then 8 else 1) else (if i < 1535 then 0 else 2)))))

private def vertexRankValue_b48 (i : ℕ) : ℕ :=
  (if i < 1552 then (if i < 1544 then (if i < 1540 then (if i < 1538 then (if i < 1537 then 1 else 3) else (if i < 1539 then 2 else 0)) else (if i < 1542 then (if i < 1541 then 2 else 7) else (if i < 1543 then 5 else 1))) else (if i < 1548 then (if i < 1546 then (if i < 1545 then 4 else 3) else (if i < 1547 then 1 else 4)) else (if i < 1550 then (if i < 1549 then 3 else 0) else (if i < 1551 then 6 else 1)))) else (if i < 1560 then (if i < 1556 then (if i < 1554 then (if i < 1553 then 0 else 2) else (if i < 1555 then 2 else 3)) else (if i < 1558 then (if i < 1557 then 3 else 2) else (if i < 1559 then 0 else 4))) else (if i < 1564 then (if i < 1562 then (if i < 1561 then 2 else 4) else (if i < 1563 then 2 else 0)) else (if i < 1566 then (if i < 1565 then 4 else 2) else (if i < 1567 then 1 else 3)))))

private def vertexRankValue_b49 (i : ℕ) : ℕ :=
  (if i < 1584 then (if i < 1576 then (if i < 1572 then (if i < 1570 then (if i < 1569 then 3 else 0) else (if i < 1571 then 3 else 1)) else (if i < 1574 then (if i < 1573 then 1 else 3) else (if i < 1575 then 1 else 1))) else (if i < 1580 then (if i < 1578 then (if i < 1577 then 8 else 4) else (if i < 1579 then 2 else 3)) else (if i < 1582 then (if i < 1581 then 2 else 0) else (if i < 1583 then 2 else 1)))) else (if i < 1592 then (if i < 1588 then (if i < 1586 then (if i < 1585 then 0 else 2) else (if i < 1587 then 3 else 3)) else (if i < 1590 then (if i < 1589 then 4 else 0) else (if i < 1591 then 4 else 1))) else (if i < 1596 then (if i < 1594 then (if i < 1593 then 3 else 1) else (if i < 1595 then 3 else 6)) else (if i < 1598 then (if i < 1597 then 5 else 0) else (if i < 1599 then 5 else 1)))))

private def vertexRankValue_b50 (i : ℕ) : ℕ :=
  (if i < 1616 then (if i < 1608 then (if i < 1604 then (if i < 1602 then (if i < 1601 then 0 else 2) else (if i < 1603 then 0 else 3)) else (if i < 1606 then (if i < 1605 then 3 else 0) else (if i < 1607 then 4 else 1))) else (if i < 1612 then (if i < 1610 then (if i < 1609 then 0 else 1) else (if i < 1611 then 2 else 1)) else (if i < 1614 then (if i < 1613 then 0 else 2) else (if i < 1615 then 0 else 1)))) else (if i < 1624 then (if i < 1620 then (if i < 1618 then (if i < 1617 then 3 else 0) else (if i < 1619 then 2 else 2)) else (if i < 1622 then (if i < 1621 then 2 else 0) else (if i < 1623 then 5 else 1))) else (if i < 1628 then (if i < 1626 then (if i < 1625 then 0 else 2) else (if i < 1627 then 0 else 4)) else (if i < 1630 then (if i < 1629 then 6 else 3) else (if i < 1631 then 5 else 2)))))

private def vertexRankValue_b51 (i : ℕ) : ℕ :=
  (if i < 1648 then (if i < 1640 then (if i < 1636 then (if i < 1634 then (if i < 1633 then 3 else 1) else (if i < 1635 then 3 else 0)) else (if i < 1638 then (if i < 1637 then 5 else 3) else (if i < 1639 then 4 else 2))) else (if i < 1644 then (if i < 1642 then (if i < 1641 then 8 else 1) else (if i < 1643 then 3 else 0)) else (if i < 1646 then (if i < 1645 then 2 else 0) else (if i < 1647 then 2 else 6)))) else (if i < 1656 then (if i < 1652 then (if i < 1650 then (if i < 1649 then 7 else 1) else (if i < 1651 then 2 else 0)) else (if i < 1654 then (if i < 1653 then 1 else 3) else (if i < 1655 then 1 else 2))) else (if i < 1660 then (if i < 1658 then (if i < 1657 then 3 else 1) else (if i < 1659 then 2 else 0)) else (if i < 1662 then (if i < 1661 then 1 else 0) else (if i < 1663 then 2 else 0)))))

private def vertexRankValue_b52 (i : ℕ) : ℕ :=
  (if i < 1680 then (if i < 1672 then (if i < 1668 then (if i < 1666 then (if i < 1665 then 1 else 5) else (if i < 1667 then 1 else 0)) else (if i < 1670 then (if i < 1669 then 4 else 1) else (if i < 1671 then 2 else 3))) else (if i < 1676 then (if i < 1674 then (if i < 1673 then 3 else 1) else (if i < 1675 then 2 else 0)) else (if i < 1678 then (if i < 1677 then 4 else 1) else (if i < 1679 then 5 else 2)))) else (if i < 1688 then (if i < 1684 then (if i < 1682 then (if i < 1681 then 0 else 3) else (if i < 1683 then 1 else 0)) else (if i < 1686 then (if i < 1685 then 5 else 1) else (if i < 1687 then 0 else 2))) else (if i < 1692 then (if i < 1690 then (if i < 1689 then 1 else 3) else (if i < 1691 then 2 else 0)) else (if i < 1694 then (if i < 1693 then 3 else 1) else (if i < 1695 then 8 else 3)))))

private def vertexRankValue_b53 (i : ℕ) : ℕ :=
  (if i < 1712 then (if i < 1704 then (if i < 1700 then (if i < 1698 then (if i < 1697 then 1 else 4) else (if i < 1699 then 2 else 0)) else (if i < 1702 then (if i < 1701 then 4 else 1) else (if i < 1703 then 0 else 2))) else (if i < 1708 then (if i < 1706 then (if i < 1705 then 2 else 3) else (if i < 1707 then 3 else 0)) else (if i < 1710 then (if i < 1709 then 6 else 4) else (if i < 1711 then 2 else 7)))) else (if i < 1720 then (if i < 1716 then (if i < 1714 then (if i < 1713 then 5 else 4) else (if i < 1715 then 2 else 1)) else (if i < 1718 then (if i < 1717 then 0 else 2) else (if i < 1719 then 3 else 3))) else (if i < 1724 then (if i < 1722 then (if i < 1721 then 6 else 0) else (if i < 1723 then 3 else 1)) else (if i < 1726 then (if i < 1725 then 2 else 0) else (if i < 1727 then 2 else 4)))))

private def vertexRankValue_b54 (i : ℕ) : ℕ :=
  (if i < 1744 then (if i < 1736 then (if i < 1732 then (if i < 1730 then (if i < 1729 then 2 else 5) else (if i < 1731 then 3 else 0)) else (if i < 1734 then (if i < 1733 then 3 else 1) else (if i < 1735 then 3 else 2))) else (if i < 1740 then (if i < 1738 then (if i < 1737 then 3 else 3) else (if i < 1739 then 4 else 0)) else (if i < 1742 then (if i < 1741 then 4 else 1) else (if i < 1743 then 5 else 2)))) else (if i < 1752 then (if i < 1748 then (if i < 1746 then (if i < 1745 then 0 else 3) else (if i < 1747 then 1 else 6)) else (if i < 1750 then (if i < 1749 then 5 else 1) else (if i < 1751 then 0 else 2))) else (if i < 1756 then (if i < 1754 then (if i < 1753 then 1 else 3) else (if i < 1755 then 2 else 0)) else (if i < 1758 then (if i < 1757 then 3 else 1) else (if i < 1759 then 4 else 2)))))

private def vertexRankValue_b55 (i : ℕ) : ℕ :=
  (if i < 1776 then (if i < 1768 then (if i < 1764 then (if i < 1762 then (if i < 1761 then 1 else 1) else (if i < 1763 then 2 else 2)) else (if i < 1766 then (if i < 1765 then 0 else 3) else (if i < 1767 then 1 else 0))) else (if i < 1772 then (if i < 1770 then (if i < 1769 then 4 else 2) else (if i < 1771 then 1 else 3)) else (if i < 1774 then (if i < 1773 then 0 else 1) else (if i < 1775 then 0 else 2)))) else (if i < 1784 then (if i < 1780 then (if i < 1778 then (if i < 1777 then 2 else 3) else (if i < 1779 then 1 else 5)) else (if i < 1782 then (if i < 1781 then 7 else 1) else (if i < 1783 then 3 else 0))) else (if i < 1788 then (if i < 1786 then (if i < 1785 then 1 else 3) else (if i < 1787 then 0 else 2)) else (if i < 1790 then (if i < 1789 then 6 else 1) else (if i < 1791 then 2 else 0)))))

private def vertexRankValue_b56 (i : ℕ) : ℕ :=
  (if i < 1808 then (if i < 1800 then (if i < 1796 then (if i < 1794 then (if i < 1793 then 1 else 3) else (if i < 1795 then 5 else 2)) else (if i < 1798 then (if i < 1797 then 0 else 1) else (if i < 1799 then 3 else 7))) else (if i < 1804 then (if i < 1802 then (if i < 1801 then 0 else 2) else (if i < 1803 then 4 else 1)) else (if i < 1806 then (if i < 1805 then 3 else 0) else (if i < 1807 then 2 else 3)))) else (if i < 1816 then (if i < 1812 then (if i < 1810 then (if i < 1809 then 0 else 2) else (if i < 1811 then 4 else 2)) else (if i < 1814 then (if i < 1813 then 3 else 1) else (if i < 1815 then 0 else 4))) else (if i < 1820 then (if i < 1818 then (if i < 1817 then 2 else 1) else (if i < 1819 then 5 else 1)) else (if i < 1822 then (if i < 1821 then 0 else 2) else (if i < 1823 then 0 else 1)))))

private def vertexRankValue_b57 (i : ℕ) : ℕ :=
  (if i < 1840 then (if i < 1832 then (if i < 1828 then (if i < 1826 then (if i < 1825 then 0 else 2) else (if i < 1827 then 0 else 1)) else (if i < 1830 then (if i < 1829 then 4 else 0) else (if i < 1831 then 4 else 4))) else (if i < 1836 then (if i < 1834 then (if i < 1833 then 2 else 8) else (if i < 1835 then 6 else 6)) else (if i < 1838 then (if i < 1837 then 5 else 0) else (if i < 1839 then 5 else 1)))) else (if i < 1848 then (if i < 1844 then (if i < 1842 then (if i < 1841 then 3 else 2) else (if i < 1843 then 7 else 3)) else (if i < 1846 then (if i < 1845 then 0 else 4) else (if i < 1847 then 2 else 0))) else (if i < 1852 then (if i < 1850 then (if i < 1849 then 3 else 6) else (if i < 1851 then 4 else 2)) else (if i < 1854 then (if i < 1853 then 1 else 3) else (if i < 1855 then 3 else 0)))))

private def vertexRankValue_b58 (i : ℕ) : ℕ :=
  (if i < 1872 then (if i < 1864 then (if i < 1860 then (if i < 1858 then (if i < 1857 then 4 else 1) else (if i < 1859 then 5 else 2)) else (if i < 1862 then (if i < 1861 then 3 else 7) else (if i < 1863 then 5 else 1))) else (if i < 1868 then (if i < 1866 then (if i < 1865 then 8 else 3) else (if i < 1867 then 1 else 0)) else (if i < 1870 then (if i < 1869 then 4 else 0) else (if i < 1871 then 6 else 1)))) else (if i < 1880 then (if i < 1876 then (if i < 1874 then (if i < 1873 then 0 else 2) else (if i < 1875 then 2 else 3)) else (if i < 1878 then (if i < 1877 then 0 else 3) else (if i < 1879 then 1 else 7))) else (if i < 1884 then (if i < 1882 then (if i < 1881 then 5 else 0) else (if i < 1883 then 4 else 2)) else (if i < 1886 then (if i < 1885 then 1 else 3) else (if i < 1887 then 2 else 0)))))

private def vertexRankValue_b59 (i : ℕ) : ℕ :=
  (if i < 1904 then (if i < 1896 then (if i < 1892 then (if i < 1890 then (if i < 1889 then 6 else 1) else (if i < 1891 then 5 else 2)) else (if i < 1894 then (if i < 1893 then 9 else 4) else (if i < 1895 then 2 else 3))) else (if i < 1900 then (if i < 1898 then (if i < 1897 then 1 else 0) else (if i < 1899 then 2 else 0)) else (if i < 1902 then (if i < 1901 then 10 else 1) else (if i < 1903 then 3 else 2)))) else (if i < 1912 then (if i < 1908 then (if i < 1906 then (if i < 1905 then 2 else 3) else (if i < 1907 then 3 else 0)) else (if i < 1910 then (if i < 1909 then 0 else 0) else (if i < 1911 then 1 else 5))) else (if i < 1916 then (if i < 1914 then (if i < 1913 then 3 else 0) else (if i < 1915 then 1 else 3)) else (if i < 1918 then (if i < 1917 then 2 else 0) else (if i < 1919 then 2 else 0)))))

private def vertexRankValue_b60 (i : ℕ) : ℕ :=
  (if i < 1936 then (if i < 1928 then (if i < 1924 then (if i < 1922 then (if i < 1921 then 1 else 2) else (if i < 1923 then 1 else 0)) else (if i < 1926 then (if i < 1925 then 1 else 3) else (if i < 1927 then 1 else 4))) else (if i < 1932 then (if i < 1930 then (if i < 1929 then 3 else 0) else (if i < 1931 then 2 else 7)) else (if i < 1934 then (if i < 1933 then 9 else 2) else (if i < 1935 then 4 else 1)))) else (if i < 1944 then (if i < 1940 then (if i < 1938 then (if i < 1937 then 2 else 3) else (if i < 1939 then 1 else 2)) else (if i < 1942 then (if i < 1941 then 8 else 1) else (if i < 1943 then 3 else 0))) else (if i < 1948 then (if i < 1946 then (if i < 1945 then 4 else 5) else (if i < 1947 then 1 else 2)) else (if i < 1950 then (if i < 1949 then 0 else 2) else (if i < 1951 then 0 else 2)))))

private def vertexRankValue_b61 (i : ℕ) : ℕ :=
  (if i < 1968 then (if i < 1960 then (if i < 1956 then (if i < 1954 then (if i < 1953 then 3 else 0) else (if i < 1955 then 0 else 3)) else (if i < 1958 then (if i < 1957 then 3 else 2) else (if i < 1959 then 3 else 1))) else (if i < 1964 then (if i < 1962 then (if i < 1961 then 2 else 3) else (if i < 1963 then 1 else 4)) else (if i < 1966 then (if i < 1965 then 0 else 2) else (if i < 1967 then 1 else 5)))) else (if i < 1976 then (if i < 1972 then (if i < 1970 then (if i < 1969 then 0 else 3) else (if i < 1971 then 0 else 1)) else (if i < 1974 then (if i < 1973 then 2 else 2) else (if i < 1975 then 0 else 1))) else (if i < 1980 then (if i < 1978 then (if i < 1977 then 1 else 0) else (if i < 1979 then 1 else 4)) else (if i < 1982 then (if i < 1981 then 4 else 8) else (if i < 1983 then 1 else 7)))))

private def vertexRankValue_b62 (i : ℕ) : ℕ :=
  (if i < 2000 then (if i < 1992 then (if i < 1988 then (if i < 1986 then (if i < 1985 then 0 else 1) else (if i < 1987 then 2 else 1)) else (if i < 1990 then (if i < 1989 then 3 else 0) else (if i < 1991 then 0 else 3))) else (if i < 1996 then (if i < 1994 then (if i < 1993 then 8 else 2) else (if i < 1995 then 6 else 1)) else (if i < 1998 then (if i < 1997 then 3 else 1) else (if i < 1999 then 3 else 4)))) else (if i < 2008 then (if i < 2004 then (if i < 2002 then (if i < 2001 then 5 else 2) else (if i < 2003 then 5 else 1)) else (if i < 2006 then (if i < 2005 then 2 else 0) else (if i < 2007 then 2 else 3))) else (if i < 2012 then (if i < 2010 then (if i < 2009 then 1 else 7) else (if i < 2011 then 0 else 7)) else (if i < 2014 then (if i < 2013 then 0 else 1) else (if i < 2015 then 2 else 0)))))

private def vertexRankValue_b63 (i : ℕ) : ℕ :=
  (if i < 2032 then (if i < 2024 then (if i < 2020 then (if i < 2018 then (if i < 2017 then 0 else 3) else (if i < 2019 then 8 else 2)) else (if i < 2022 then (if i < 2021 then 8 else 1) else (if i < 2023 then 3 else 0))) else (if i < 2028 then (if i < 2026 then (if i < 2025 then 3 else 2) else (if i < 2027 then 1 else 4)) else (if i < 2030 then (if i < 2029 then 2 else 5) else (if i < 2031 then 3 else 0)))) else (if i < 2040 then (if i < 2036 then (if i < 2034 then (if i < 2033 then 1 else 0) else (if i < 2035 then 4 else 4)) else (if i < 2038 then (if i < 2037 then 2 else 6) else (if i < 2039 then 4 else 3))) else (if i < 2044 then (if i < 2042 then (if i < 2041 then 2 else 3) else (if i < 2043 then 5 else 0)) else (if i < 2046 then (if i < 2045 then 3 else 1) else (if i < 2047 then 5 else 2)))))

private def vertexRankValue_b64 (i : ℕ) : ℕ :=
  (if i < 2064 then (if i < 2056 then (if i < 2052 then (if i < 2050 then (if i < 2049 then 0 else 4) else (if i < 2051 then 2 else 4)) else (if i < 2054 then (if i < 2053 then 2 else 6) else (if i < 2055 then 4 else 2))) else (if i < 2060 then (if i < 2058 then (if i < 2057 then 1 else 3) else (if i < 2059 then 3 else 0)) else (if i < 2062 then (if i < 2061 then 3 else 1) else (if i < 2063 then 5 else 2)))) else (if i < 2072 then (if i < 2068 then (if i < 2066 then (if i < 2065 then 3 else 8) else (if i < 2067 then 6 else 1)) else (if i < 2070 then (if i < 2069 then 8 else 3) else (if i < 2071 then 1 else 0))) else (if i < 2076 then (if i < 2074 then (if i < 2073 then 4 else 0) else (if i < 2075 then 7 else 1)) else (if i < 2078 then (if i < 2077 then 0 else 2) else (if i < 2079 then 2 else 3)))))

private def vertexRankValue_b65 (i : ℕ) : ℕ :=
  (if i < 2096 then (if i < 2088 then (if i < 2084 then (if i < 2082 then (if i < 2081 then 0 else 3) else (if i < 2083 then 1 else 7)) else (if i < 2086 then (if i < 2085 then 5 else 0) else (if i < 2087 then 4 else 2))) else (if i < 2092 then (if i < 2090 then (if i < 2089 then 1 else 3) else (if i < 2091 then 2 else 0)) else (if i < 2094 then (if i < 2093 then 6 else 1) else (if i < 2095 then 5 else 2)))) else (if i < 2104 then (if i < 2100 then (if i < 2098 then (if i < 2097 then 7 else 4) else (if i < 2099 then 2 else 3)) else (if i < 2102 then (if i < 2101 then 1 else 0) else (if i < 2103 then 2 else 0))) else (if i < 2108 then (if i < 2106 then (if i < 2105 then 8 else 2) else (if i < 2107 then 3 else 3)) else (if i < 2110 then (if i < 2109 then 2 else 0) else (if i < 2111 then 3 else 1)))))

private def vertexRankValue_b66 (i : ℕ) : ℕ :=
  (if i < 2128 then (if i < 2120 then (if i < 2116 then (if i < 2114 then (if i < 2113 then 0 else 0) else (if i < 2115 then 1 else 5)) else (if i < 2118 then (if i < 2117 then 3 else 0) else (if i < 2119 then 1 else 3))) else (if i < 2124 then (if i < 2122 then (if i < 2121 then 2 else 0) else (if i < 2123 then 2 else 0)) else (if i < 2126 then (if i < 2125 then 1 else 2) else (if i < 2127 then 1 else 0)))) else (if i < 2136 then (if i < 2132 then (if i < 2130 then (if i < 2129 then 1 else 3) else (if i < 2131 then 1 else 4)) else (if i < 2134 then (if i < 2133 then 3 else 0) else (if i < 2135 then 2 else 7))) else (if i < 2140 then (if i < 2138 then (if i < 2137 then 0 else 2) else (if i < 2139 then 4 else 1)) else (if i < 2142 then (if i < 2141 then 2 else 3) else (if i < 2143 then 1 else 2)))))

private def vertexRankValue_b67 (i : ℕ) : ℕ :=
  (if i < 2160 then (if i < 2152 then (if i < 2148 then (if i < 2146 then (if i < 2145 then 8 else 1) else (if i < 2147 then 3 else 0)) else (if i < 2150 then (if i < 2149 then 5 else 0) else (if i < 2151 then 2 else 3))) else (if i < 2156 then (if i < 2154 then (if i < 2153 then 1 else 2) else (if i < 2155 then 0 else 3)) else (if i < 2158 then (if i < 2157 then 4 else 0) else (if i < 2159 then 1 else 3)))) else (if i < 2168 then (if i < 2164 then (if i < 2162 then (if i < 2161 then 0 else 2) else (if i < 2163 then 3 else 1)) else (if i < 2166 then (if i < 2165 then 1 else 3) else (if i < 2167 then 0 else 5))) else (if i < 2172 then (if i < 2170 then (if i < 2169 then 0 else 2) else (if i < 2171 then 1 else 5)) else (if i < 2174 then (if i < 2173 then 0 else 4) else (if i < 2175 then 0 else 1)))))

private def vertexRankValue_b68 (i : ℕ) : ℕ :=
  (if i < 2192 then (if i < 2184 then (if i < 2180 then (if i < 2178 then (if i < 2177 then 3 else 2) else (if i < 2179 then 0 else 2)) else (if i < 2182 then (if i < 2181 then 1 else 4) else (if i < 2183 then 1 else 3))) else (if i < 2188 then (if i < 2186 then (if i < 2185 then 4 else 0) else (if i < 2187 then 4 else 1)) else (if i < 2190 then (if i < 2189 then 4 else 1) else (if i < 2191 then 8 else 6)))) else (if i < 2200 then (if i < 2196 then (if i < 2194 then (if i < 2193 then 5 else 0) else (if i < 2195 then 5 else 1)) else (if i < 2198 then (if i < 2197 then 0 else 2) else (if i < 2199 then 0 else 3))) else (if i < 2204 then (if i < 2202 then (if i < 2201 then 2 else 6) else (if i < 2203 then 4 else 1)) else (if i < 2206 then (if i < 2205 then 4 else 2) else (if i < 2207 then 0 else 4)))))

private def vertexRankValue_b69 (i : ℕ) : ℕ :=
  (if i < 2224 then (if i < 2216 then (if i < 2212 then (if i < 2210 then (if i < 2209 then 3 else 0) else (if i < 2211 then 5 else 1)) else (if i < 2214 then (if i < 2213 then 0 else 2) else (if i < 2215 then 1 else 3))) else (if i < 2220 then (if i < 2218 then (if i < 2217 then 5 else 2) else (if i < 2219 then 0 else 3)) else (if i < 2222 then (if i < 2221 then 1 else 3) else (if i < 2223 then 1 else 0)))) else (if i < 2232 then (if i < 2228 then (if i < 2226 then (if i < 2225 then 6 else 1) else (if i < 2227 then 1 else 2)) else (if i < 2230 then (if i < 2229 then 2 else 3) else (if i < 2231 then 2 else 0))) else (if i < 2236 then (if i < 2234 then (if i < 2233 then 1 else 3) else (if i < 2235 then 1 else 0)) else (if i < 2238 then (if i < 2237 then 7 else 3) else (if i < 2239 then 1 else 3)))))

private def vertexRankValue_b70 (i : ℕ) : ℕ :=
  (if i < 2256 then (if i < 2248 then (if i < 2244 then (if i < 2242 then (if i < 2241 then 2 else 0) else (if i < 2243 then 2 else 1)) else (if i < 2246 then (if i < 2245 then 8 else 2) else (if i < 2247 then 2 else 3))) else (if i < 2252 then (if i < 2250 then (if i < 2249 then 2 else 0) else (if i < 2251 then 4 else 1)) else (if i < 2254 then (if i < 2253 then 3 else 0) else (if i < 2255 then 2 else 4)))) else (if i < 2264 then (if i < 2260 then (if i < 2258 then (if i < 2257 then 3 else 0) else (if i < 2259 then 5 else 1)) else (if i < 2262 then (if i < 2261 then 0 else 2) else (if i < 2263 then 3 else 3))) else (if i < 2268 then (if i < 2266 then (if i < 2265 then 2 else 0) else (if i < 2267 then 3 else 1)) else (if i < 2270 then (if i < 2269 then 0 else 1) else (if i < 2271 then 2 else 0)))))

private def vertexRankValue_b71 (i : ℕ) : ℕ :=
  (if i < 2288 then (if i < 2280 then (if i < 2276 then (if i < 2274 then (if i < 2273 then 0 else 2) else (if i < 2275 then 5 else 1)) else (if i < 2278 then (if i < 2277 then 3 else 0) else (if i < 2279 then 2 else 2))) else (if i < 2284 then (if i < 2282 then (if i < 2281 then 1 else 0) else (if i < 2283 then 4 else 1)) else (if i < 2286 then (if i < 2285 then 0 else 2) else (if i < 2287 then 0 else 3)))) else (if i < 2296 then (if i < 2292 then (if i < 2290 then (if i < 2289 then 5 else 4) else (if i < 2291 then 0 else 2)) else (if i < 2294 then (if i < 2293 then 3 else 1) else (if i < 2295 then 3 else 0))) else (if i < 2300 then (if i < 2298 then (if i < 2297 then 4 else 3) else (if i < 2299 then 5 else 2)) else (if i < 2302 then (if i < 2301 then 7 else 1) else (if i < 2303 then 3 else 0)))))

private def vertexRankValue_b72 (i : ℕ) : ℕ :=
  (if i < 2320 then (if i < 2312 then (if i < 2308 then (if i < 2306 then (if i < 2305 then 2 else 3) else (if i < 2307 then 1 else 5)) else (if i < 2310 then (if i < 2309 then 6 else 1) else (if i < 2311 then 2 else 0))) else (if i < 2316 then (if i < 2314 then (if i < 2313 then 1 else 3) else (if i < 2315 then 0 else 2)) else (if i < 2318 then (if i < 2317 then 3 else 1) else (if i < 2319 then 2 else 0)))) else (if i < 2328 then (if i < 2324 then (if i < 2322 then (if i < 2321 then 1 else 0) else (if i < 2323 then 2 else 1)) else (if i < 2326 then (if i < 2325 then 1 else 5) else (if i < 2327 then 2 else 0))) else (if i < 2332 then (if i < 2330 then (if i < 2329 then 4 else 1) else (if i < 2331 then 2 else 3)) else (if i < 2334 then (if i < 2333 then 2 else 1) else (if i < 2335 then 3 else 0)))))

private def vertexRankValue_b73 (i : ℕ) : ℕ :=
  (if i < 2352 then (if i < 2344 then (if i < 2340 then (if i < 2338 then (if i < 2337 then 1 else 3) else (if i < 2339 then 1 else 4)) else (if i < 2342 then (if i < 2341 then 2 else 6) else (if i < 2343 then 4 else 3))) else (if i < 2348 then (if i < 2346 then (if i < 2345 then 2 else 3) else (if i < 2347 then 2 else 0)) else (if i < 2350 then (if i < 2349 then 3 else 1) else (if i < 2351 then 5 else 2)))) else (if i < 2360 then (if i < 2356 then (if i < 2354 then (if i < 2353 then 3 else 1) else (if i < 2355 then 8 else 4)) else (if i < 2358 then (if i < 2357 then 2 else 5) else (if i < 2359 then 3 else 0))) else (if i < 2364 then (if i < 2362 then (if i < 2361 then 4 else 1) else (if i < 2363 then 0 else 2)) else (if i < 2366 then (if i < 2365 then 3 else 3) else (if i < 2367 then 4 else 0)))))

private def vertexRankValue_b74 (i : ℕ) : ℕ :=
  (if i < 2384 then (if i < 2376 then (if i < 2372 then (if i < 2370 then (if i < 2369 then 1 else 4) else (if i < 2371 then 2 else 7)) else (if i < 2374 then (if i < 2373 then 5 else 0) else (if i < 2375 then 4 else 3))) else (if i < 2380 then (if i < 2378 then (if i < 2377 then 2 else 3) else (if i < 2379 then 3 else 0)) else (if i < 2382 then (if i < 2381 then 6 else 1) else (if i < 2383 then 5 else 2)))) else (if i < 2392 then (if i < 2388 then (if i < 2386 then (if i < 2385 then 3 else 2) else (if i < 2387 then 0 else 4)) else (if i < 2390 then (if i < 2389 then 2 else 5) else (if i < 2391 then 3 else 1))) else (if i < 2396 then (if i < 2394 then (if i < 2393 then 0 else 2) else (if i < 2395 then 1 else 3)) else (if i < 2398 then (if i < 2397 then 3 else 0) else (if i < 2399 then 4 else 1)))))

private def vertexRankValue_b75 (i : ℕ) : ℕ :=
  (if i < 2416 then (if i < 2408 then (if i < 2404 then (if i < 2402 then (if i < 2401 then 7 else 3) else (if i < 2403 then 1 else 2)) else (if i < 2406 then (if i < 2405 then 0 else 3) else (if i < 2407 then 1 else 9))) else (if i < 2412 then (if i < 2410 then (if i < 2409 then 8 else 1) else (if i < 2411 then 2 else 2)) else (if i < 2414 then (if i < 2413 then 1 else 3) else (if i < 2415 then 2 else 0)))) else (if i < 2424 then (if i < 2420 then (if i < 2418 then (if i < 2417 then 0 else 3) else (if i < 2419 then 1 else 4)) else (if i < 2422 then (if i < 2421 then 2 else 2) else (if i < 2423 then 0 else 2))) else (if i < 2428 then (if i < 2426 then (if i < 2425 then 1 else 5) else (if i < 2427 then 1 else 0)) else (if i < 2430 then (if i < 2429 then 0 else 2) else (if i < 2431 then 1 else 3)))))

private def vertexRankValue_b76 (i : ℕ) : ℕ :=
  (if i < 2448 then (if i < 2440 then (if i < 2436 then (if i < 2434 then (if i < 2433 then 0 else 1) else (if i < 2435 then 0 else 2)) else (if i < 2438 then (if i < 2437 then 2 else 3) else (if i < 2439 then 1 else 6))) else (if i < 2444 then (if i < 2442 then (if i < 2441 then 8 else 1) else (if i < 2443 then 3 else 0)) else (if i < 2446 then (if i < 2445 then 1 else 3) else (if i < 2447 then 0 else 2)))) else (if i < 2456 then (if i < 2452 then (if i < 2450 then (if i < 2449 then 7 else 1) else (if i < 2451 then 2 else 0)) else (if i < 2454 then (if i < 2453 then 1 else 3) else (if i < 2455 then 5 else 2))) else (if i < 2460 then (if i < 2458 then (if i < 2457 then 0 else 2) else (if i < 2459 then 0 else 7)) else (if i < 2462 then (if i < 2461 then 0 else 2) else (if i < 2463 then 4 else 1)))))

private def vertexRankValue_b77 (i : ℕ) : ℕ :=
  (if i < 2480 then (if i < 2472 then (if i < 2468 then (if i < 2466 then (if i < 2465 then 3 else 0) else (if i < 2467 then 3 else 3)) else (if i < 2470 then (if i < 2469 then 1 else 2) else (if i < 2471 then 0 else 2))) else (if i < 2476 then (if i < 2474 then (if i < 2473 then 3 else 1) else (if i < 2475 then 0 else 4)) else (if i < 2478 then (if i < 2477 then 2 else 1) else (if i < 2479 then 5 else 1)))) else (if i < 2488 then (if i < 2484 then (if i < 2482 then (if i < 2481 then 0 else 2) else (if i < 2483 then 0 else 1)) else (if i < 2486 then (if i < 2485 then 1 else 3) else (if i < 2487 then 0 else 2))) else (if i < 2492 then (if i < 2490 then (if i < 2489 then 1 else 6) else (if i < 2491 then 8 else 5)) else (if i < 2494 then (if i < 2493 then 7 else 1) else (if i < 2495 then 2 else 3)))))

private def vertexRankValue_b78 (i : ℕ) : ℕ :=
  (if i < 2512 then (if i < 2504 then (if i < 2500 then (if i < 2498 then (if i < 2497 then 0 else 2) else (if i < 2499 then 7 else 1)) else (if i < 2502 then (if i < 2501 then 6 else 0) else (if i < 2503 then 4 else 0))) else (if i < 2508 then (if i < 2506 then (if i < 2505 then 2 else 10) else (if i < 2507 then 1 else 3)) else (if i < 2510 then (if i < 2509 then 4 else 1) else (if i < 2511 then 3 else 0)))) else (if i < 2520 then (if i < 2516 then (if i < 2514 then (if i < 2513 then 1 else 3) else (if i < 2515 then 0 else 2)) else (if i < 2518 then (if i < 2517 then 6 else 1) else (if i < 2519 then 3 else 1))) else (if i < 2524 then (if i < 2522 then (if i < 2521 then 3 else 4) else (if i < 2523 then 0 else 2)) else (if i < 2526 then (if i < 2525 then 5 else 1) else (if i < 2527 then 2 else 0)))))

private def vertexRankValue_b79 (i : ℕ) : ℕ :=
  (if i < 2544 then (if i < 2536 then (if i < 2532 then (if i < 2530 then (if i < 2529 then 2 else 3) else (if i < 2531 then 1 else 3)) else (if i < 2534 then (if i < 2533 then 2 else 0) else (if i < 2535 then 4 else 2))) else (if i < 2540 then (if i < 2538 then (if i < 2537 then 0 else 2) else (if i < 2539 then 1 else 9)) else (if i < 2542 then (if i < 2541 then 0 else 3) else (if i < 2543 then 1 else 3)))) else (if i < 2552 then (if i < 2548 then (if i < 2546 then (if i < 2545 then 0 else 1) else (if i < 2547 then 2 else 0)) else (if i < 2550 then (if i < 2549 then 0 else 3) else (if i < 2551 then 4 else 2))) else (if i < 2556 then (if i < 2554 then (if i < 2553 then 4 else 1) else (if i < 2555 then 1 else 3)) else (if i < 2558 then (if i < 2557 then 2 else 2) else (if i < 2559 then 1 else 3)))))

private def vertexRankValue_b80 (i : ℕ) : ℕ :=
  (if i < 2576 then (if i < 2568 then (if i < 2564 then (if i < 2562 then (if i < 2561 then 2 else 0) else (if i < 2563 then 2 else 1)) else (if i < 2566 then (if i < 2565 then 3 else 2) else (if i < 2567 then 0 else 1))) else (if i < 2572 then (if i < 2570 then (if i < 2569 then 2 else 6) else (if i < 2571 then 0 else 2)) else (if i < 2574 then (if i < 2573 then 10 else 1) else (if i < 2575 then 2 else 0)))) else (if i < 2584 then (if i < 2580 then (if i < 2578 then (if i < 2577 then 1 else 3) else (if i < 2579 then 10 else 1)) else (if i < 2582 then (if i < 2581 then 2 else 6) else (if i < 2583 then 0 else 2))) else (if i < 2588 then (if i < 2586 then (if i < 2585 then 9 else 1) else (if i < 2587 then 2 else 0)) else (if i < 2590 then (if i < 2589 then 1 else 3) else (if i < 2591 then 7 else 1)))))

private def vertexRankValue_b81 (i : ℕ) : ℕ :=
  (if i < 2608 then (if i < 2600 then (if i < 2596 then (if i < 2594 then (if i < 2593 then 2 else 5) else (if i < 2595 then 6 else 2)) else (if i < 2598 then (if i < 2597 then 6 else 1) else (if i < 2599 then 2 else 0))) else (if i < 2604 then (if i < 2602 then (if i < 2601 then 1 else 3) else (if i < 2603 then 10 else 2)) else (if i < 2606 then (if i < 2605 then 5 else 6) else (if i < 2607 then 0 else 2)))) else (if i < 2616 then (if i < 2612 then (if i < 2610 then (if i < 2609 then 9 else 1) else (if i < 2611 then 3 else 0)) else (if i < 2614 then (if i < 2613 then 4 else 3) else (if i < 2615 then 9 else 1))) else (if i < 2620 then (if i < 2618 then (if i < 2617 then 3 else 6) else (if i < 2619 then 0 else 2)) else (if i < 2622 then (if i < 2621 then 8 else 1) else (if i < 2623 then 2 else 0)))))

private def vertexRankValue_b82 (i : ℕ) : ℕ :=
  (if i < 2635 then (if i < 2629 then (if i < 2626 then (if i < 2625 then 2 else 3) else (if i < 2627 then 1 else (if i < 2628 then 0 else 1))) else (if i < 2632 then (if i < 2630 then 0 else (if i < 2631 then 1 else 0)) else (if i < 2633 then 1 else (if i < 2634 then 0 else 1)))) else (if i < 2640 then (if i < 2637 then (if i < 2636 then 1 else 0) else (if i < 2638 then 4 else (if i < 2639 then 0 else 3))) else (if i < 2643 then (if i < 2641 then 0 else (if i < 2642 then 3 else 0)) else (if i < 2644 then 0 else (if i < 2645 then 1 else 0)))))

private def vertexRankValue_n0_0 (i : ℕ) : ℕ := if i < 32 then vertexRankValue_b0 i else vertexRankValue_b1 i

private def vertexRankValue_n0_1 (i : ℕ) : ℕ := if i < 96 then vertexRankValue_b2 i else vertexRankValue_b3 i

private def vertexRankValue_n0_2 (i : ℕ) : ℕ := if i < 160 then vertexRankValue_b4 i else vertexRankValue_b5 i

private def vertexRankValue_n0_3 (i : ℕ) : ℕ := if i < 224 then vertexRankValue_b6 i else vertexRankValue_b7 i

private def vertexRankValue_n0_4 (i : ℕ) : ℕ := if i < 288 then vertexRankValue_b8 i else vertexRankValue_b9 i

private def vertexRankValue_n0_5 (i : ℕ) : ℕ := if i < 352 then vertexRankValue_b10 i else vertexRankValue_b11 i

private def vertexRankValue_n0_6 (i : ℕ) : ℕ := if i < 416 then vertexRankValue_b12 i else vertexRankValue_b13 i

private def vertexRankValue_n0_7 (i : ℕ) : ℕ := if i < 480 then vertexRankValue_b14 i else vertexRankValue_b15 i

private def vertexRankValue_n0_8 (i : ℕ) : ℕ := if i < 544 then vertexRankValue_b16 i else vertexRankValue_b17 i

private def vertexRankValue_n0_9 (i : ℕ) : ℕ := if i < 608 then vertexRankValue_b18 i else vertexRankValue_b19 i

private def vertexRankValue_n0_10 (i : ℕ) : ℕ := if i < 672 then vertexRankValue_b20 i else vertexRankValue_b21 i

private def vertexRankValue_n0_11 (i : ℕ) : ℕ := if i < 736 then vertexRankValue_b22 i else vertexRankValue_b23 i

private def vertexRankValue_n0_12 (i : ℕ) : ℕ := if i < 800 then vertexRankValue_b24 i else vertexRankValue_b25 i

private def vertexRankValue_n0_13 (i : ℕ) : ℕ := if i < 864 then vertexRankValue_b26 i else vertexRankValue_b27 i

private def vertexRankValue_n0_14 (i : ℕ) : ℕ := if i < 928 then vertexRankValue_b28 i else vertexRankValue_b29 i

private def vertexRankValue_n0_15 (i : ℕ) : ℕ := if i < 992 then vertexRankValue_b30 i else vertexRankValue_b31 i

private def vertexRankValue_n0_16 (i : ℕ) : ℕ := if i < 1056 then vertexRankValue_b32 i else vertexRankValue_b33 i

private def vertexRankValue_n0_17 (i : ℕ) : ℕ := if i < 1120 then vertexRankValue_b34 i else vertexRankValue_b35 i

private def vertexRankValue_n0_18 (i : ℕ) : ℕ := if i < 1184 then vertexRankValue_b36 i else vertexRankValue_b37 i

private def vertexRankValue_n0_19 (i : ℕ) : ℕ := if i < 1248 then vertexRankValue_b38 i else vertexRankValue_b39 i

private def vertexRankValue_n0_20 (i : ℕ) : ℕ := if i < 1312 then vertexRankValue_b40 i else vertexRankValue_b41 i

private def vertexRankValue_n0_21 (i : ℕ) : ℕ := if i < 1376 then vertexRankValue_b42 i else vertexRankValue_b43 i

private def vertexRankValue_n0_22 (i : ℕ) : ℕ := if i < 1440 then vertexRankValue_b44 i else vertexRankValue_b45 i

private def vertexRankValue_n0_23 (i : ℕ) : ℕ := if i < 1504 then vertexRankValue_b46 i else vertexRankValue_b47 i

private def vertexRankValue_n0_24 (i : ℕ) : ℕ := if i < 1568 then vertexRankValue_b48 i else vertexRankValue_b49 i

private def vertexRankValue_n0_25 (i : ℕ) : ℕ := if i < 1632 then vertexRankValue_b50 i else vertexRankValue_b51 i

private def vertexRankValue_n0_26 (i : ℕ) : ℕ := if i < 1696 then vertexRankValue_b52 i else vertexRankValue_b53 i

private def vertexRankValue_n0_27 (i : ℕ) : ℕ := if i < 1760 then vertexRankValue_b54 i else vertexRankValue_b55 i

private def vertexRankValue_n0_28 (i : ℕ) : ℕ := if i < 1824 then vertexRankValue_b56 i else vertexRankValue_b57 i

private def vertexRankValue_n0_29 (i : ℕ) : ℕ := if i < 1888 then vertexRankValue_b58 i else vertexRankValue_b59 i

private def vertexRankValue_n0_30 (i : ℕ) : ℕ := if i < 1952 then vertexRankValue_b60 i else vertexRankValue_b61 i

private def vertexRankValue_n0_31 (i : ℕ) : ℕ := if i < 2016 then vertexRankValue_b62 i else vertexRankValue_b63 i

private def vertexRankValue_n0_32 (i : ℕ) : ℕ := if i < 2080 then vertexRankValue_b64 i else vertexRankValue_b65 i

private def vertexRankValue_n0_33 (i : ℕ) : ℕ := if i < 2144 then vertexRankValue_b66 i else vertexRankValue_b67 i

private def vertexRankValue_n0_34 (i : ℕ) : ℕ := if i < 2208 then vertexRankValue_b68 i else vertexRankValue_b69 i

private def vertexRankValue_n0_35 (i : ℕ) : ℕ := if i < 2272 then vertexRankValue_b70 i else vertexRankValue_b71 i

private def vertexRankValue_n0_36 (i : ℕ) : ℕ := if i < 2336 then vertexRankValue_b72 i else vertexRankValue_b73 i

private def vertexRankValue_n0_37 (i : ℕ) : ℕ := if i < 2400 then vertexRankValue_b74 i else vertexRankValue_b75 i

private def vertexRankValue_n0_38 (i : ℕ) : ℕ := if i < 2464 then vertexRankValue_b76 i else vertexRankValue_b77 i

private def vertexRankValue_n0_39 (i : ℕ) : ℕ := if i < 2528 then vertexRankValue_b78 i else vertexRankValue_b79 i

private def vertexRankValue_n0_40 (i : ℕ) : ℕ := if i < 2592 then vertexRankValue_b80 i else vertexRankValue_b81 i

private def vertexRankValue_n1_0 (i : ℕ) : ℕ := if i < 64 then vertexRankValue_n0_0 i else vertexRankValue_n0_1 i

private def vertexRankValue_n1_1 (i : ℕ) : ℕ := if i < 192 then vertexRankValue_n0_2 i else vertexRankValue_n0_3 i

private def vertexRankValue_n1_2 (i : ℕ) : ℕ := if i < 320 then vertexRankValue_n0_4 i else vertexRankValue_n0_5 i

private def vertexRankValue_n1_3 (i : ℕ) : ℕ := if i < 448 then vertexRankValue_n0_6 i else vertexRankValue_n0_7 i

private def vertexRankValue_n1_4 (i : ℕ) : ℕ := if i < 576 then vertexRankValue_n0_8 i else vertexRankValue_n0_9 i

private def vertexRankValue_n1_5 (i : ℕ) : ℕ := if i < 704 then vertexRankValue_n0_10 i else vertexRankValue_n0_11 i

private def vertexRankValue_n1_6 (i : ℕ) : ℕ := if i < 832 then vertexRankValue_n0_12 i else vertexRankValue_n0_13 i

private def vertexRankValue_n1_7 (i : ℕ) : ℕ := if i < 960 then vertexRankValue_n0_14 i else vertexRankValue_n0_15 i

private def vertexRankValue_n1_8 (i : ℕ) : ℕ := if i < 1088 then vertexRankValue_n0_16 i else vertexRankValue_n0_17 i

private def vertexRankValue_n1_9 (i : ℕ) : ℕ := if i < 1216 then vertexRankValue_n0_18 i else vertexRankValue_n0_19 i

private def vertexRankValue_n1_10 (i : ℕ) : ℕ := if i < 1344 then vertexRankValue_n0_20 i else vertexRankValue_n0_21 i

private def vertexRankValue_n1_11 (i : ℕ) : ℕ := if i < 1472 then vertexRankValue_n0_22 i else vertexRankValue_n0_23 i

private def vertexRankValue_n1_12 (i : ℕ) : ℕ := if i < 1600 then vertexRankValue_n0_24 i else vertexRankValue_n0_25 i

private def vertexRankValue_n1_13 (i : ℕ) : ℕ := if i < 1728 then vertexRankValue_n0_26 i else vertexRankValue_n0_27 i

private def vertexRankValue_n1_14 (i : ℕ) : ℕ := if i < 1856 then vertexRankValue_n0_28 i else vertexRankValue_n0_29 i

private def vertexRankValue_n1_15 (i : ℕ) : ℕ := if i < 1984 then vertexRankValue_n0_30 i else vertexRankValue_n0_31 i

private def vertexRankValue_n1_16 (i : ℕ) : ℕ := if i < 2112 then vertexRankValue_n0_32 i else vertexRankValue_n0_33 i

private def vertexRankValue_n1_17 (i : ℕ) : ℕ := if i < 2240 then vertexRankValue_n0_34 i else vertexRankValue_n0_35 i

private def vertexRankValue_n1_18 (i : ℕ) : ℕ := if i < 2368 then vertexRankValue_n0_36 i else vertexRankValue_n0_37 i

private def vertexRankValue_n1_19 (i : ℕ) : ℕ := if i < 2496 then vertexRankValue_n0_38 i else vertexRankValue_n0_39 i

private def vertexRankValue_n1_20 (i : ℕ) : ℕ := if i < 2624 then vertexRankValue_n0_40 i else vertexRankValue_b82 i

private def vertexRankValue_n2_0 (i : ℕ) : ℕ := if i < 128 then vertexRankValue_n1_0 i else vertexRankValue_n1_1 i

private def vertexRankValue_n2_1 (i : ℕ) : ℕ := if i < 384 then vertexRankValue_n1_2 i else vertexRankValue_n1_3 i

private def vertexRankValue_n2_2 (i : ℕ) : ℕ := if i < 640 then vertexRankValue_n1_4 i else vertexRankValue_n1_5 i

private def vertexRankValue_n2_3 (i : ℕ) : ℕ := if i < 896 then vertexRankValue_n1_6 i else vertexRankValue_n1_7 i

private def vertexRankValue_n2_4 (i : ℕ) : ℕ := if i < 1152 then vertexRankValue_n1_8 i else vertexRankValue_n1_9 i

private def vertexRankValue_n2_5 (i : ℕ) : ℕ := if i < 1408 then vertexRankValue_n1_10 i else vertexRankValue_n1_11 i

private def vertexRankValue_n2_6 (i : ℕ) : ℕ := if i < 1664 then vertexRankValue_n1_12 i else vertexRankValue_n1_13 i

private def vertexRankValue_n2_7 (i : ℕ) : ℕ := if i < 1920 then vertexRankValue_n1_14 i else vertexRankValue_n1_15 i

private def vertexRankValue_n2_8 (i : ℕ) : ℕ := if i < 2176 then vertexRankValue_n1_16 i else vertexRankValue_n1_17 i

private def vertexRankValue_n2_9 (i : ℕ) : ℕ := if i < 2432 then vertexRankValue_n1_18 i else vertexRankValue_n1_19 i

private def vertexRankValue_n3_0 (i : ℕ) : ℕ := if i < 256 then vertexRankValue_n2_0 i else vertexRankValue_n2_1 i

private def vertexRankValue_n3_1 (i : ℕ) : ℕ := if i < 768 then vertexRankValue_n2_2 i else vertexRankValue_n2_3 i

private def vertexRankValue_n3_2 (i : ℕ) : ℕ := if i < 1280 then vertexRankValue_n2_4 i else vertexRankValue_n2_5 i

private def vertexRankValue_n3_3 (i : ℕ) : ℕ := if i < 1792 then vertexRankValue_n2_6 i else vertexRankValue_n2_7 i

private def vertexRankValue_n3_4 (i : ℕ) : ℕ := if i < 2304 then vertexRankValue_n2_8 i else vertexRankValue_n2_9 i

private def vertexRankValue_n4_0 (i : ℕ) : ℕ := if i < 512 then vertexRankValue_n3_0 i else vertexRankValue_n3_1 i

private def vertexRankValue_n4_1 (i : ℕ) : ℕ := if i < 1536 then vertexRankValue_n3_2 i else vertexRankValue_n3_3 i

private def vertexRankValue_n4_2 (i : ℕ) : ℕ := if i < 2560 then vertexRankValue_n3_4 i else vertexRankValue_n1_20 i

private def vertexRankValue_n5_0 (i : ℕ) : ℕ := if i < 1024 then vertexRankValue_n4_0 i else vertexRankValue_n4_1 i

private def vertexRankValue_n6_0 (i : ℕ) : ℕ := if i < 2048 then vertexRankValue_n5_0 i else vertexRankValue_n4_2 i

def vertexRankValue (i : ℕ) : ℕ := vertexRankValue_n6_0 i

end PlanarHom.ColoringMacroFaces.WireFramed
