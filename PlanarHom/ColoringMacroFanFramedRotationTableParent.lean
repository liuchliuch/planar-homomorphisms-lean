import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.FanFramed
private def parentValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 1056) else (if i < 3 then 1035 else 48)) else (if i < 6 then (if i < 5 then 18 else 252) else (if i < 7 then 222 else 321))) else (if i < 12 then (if i < 10 then (if i < 9 then 558 else 528) else (if i < 11 then 762 else 732)) else (if i < 14 then (if i < 13 then 864 else 79) else (if i < 15 then 15 else 20)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 13 else 22) else (if i < 19 then 80 else 82)) else (if i < 22 then (if i < 21 then 18 else 19) else (if i < 23 then 19 else 18))) else (if i < 28 then (if i < 26 then (if i < 25 then 19 else 15) else (if i < 27 then 20 else 21)) else (if i < 30 then (if i < 29 then 30 else 18) else (if i < 31 then 18 else 30)))))

private def parentValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 26 else 30) else (if i < 35 then 26 else 18)) else (if i < 38 then (if i < 37 then 19 else 19) else (if i < 39 then 37 else 13))) else (if i < 44 then (if i < 42 then (if i < 41 then 22 else 37) else (if i < 43 then 36 else 39)) else (if i < 46 then (if i < 45 then 19 else 39) else (if i < 47 then 79 else 84)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 47 else 85) else (if i < 51 then 49 else 3)) else (if i < 54 then (if i < 53 then 54 else 48) else (if i < 55 then 50 else 50))) else (if i < 60 then (if i < 58 then (if i < 57 then 48 else 50) else (if i < 59 then 47 else 50)) else (if i < 62 then (if i < 61 then 50 else 60) else (if i < 63 then 54 else 53)))))

private def parentValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 60 else 59) else (if i < 67 then 63 else 50)) else (if i < 70 then (if i < 69 then 51 else 55) else (if i < 71 then 46 else 73))) else (if i < 76 then (if i < 74 then (if i < 73 then 49 else 49) else (if i < 75 then 73 else 71)) else (if i < 78 then (if i < 77 then 73 else 70) else (if i < 79 then 49 else 85)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 81 else 0) else (if i < 83 then 83 else 81)) else (if i < 86 then (if i < 85 then 0 else 84) else (if i < 87 then 81 else 83))) else (if i < 92 then (if i < 90 then (if i < 89 then 83 else 0) else (if i < 91 then 83 else 81)) else (if i < 94 then (if i < 93 then 86 else 83) else (if i < 95 then 96 else 84)))))

private def parentValue_b3 (i : ℕ) : ℕ :=
  (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 84 else 96) else (if i < 99 then 92 else 96)) else (if i < 102 then (if i < 101 then 83 else 84) else (if i < 103 then 85 else 85))) else (if i < 108 then (if i < 106 then (if i < 105 then 103 else 82) else (if i < 107 then 88 else 103)) else (if i < 110 then (if i < 109 then 102 else 106) else (if i < 111 then 85 else 82)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 16 else 84) else (if i < 115 then 80 else 118)) else (if i < 118 then (if i < 117 then 117 else 1) else (if i < 119 then 119 else 117))) else (if i < 124 then (if i < 122 then (if i < 121 then 1 else 120) else (if i < 123 then 117 else 119)) else (if i < 126 then (if i < 125 then 119 else 1) else (if i < 127 then 119 else 117)))))

private def parentValue_b4 (i : ℕ) : ℕ :=
  (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 122 else 119) else (if i < 131 then 132 else 120)) else (if i < 134 then (if i < 133 then 120 else 132) else (if i < 135 then 128 else 132))) else (if i < 140 then (if i < 138 then (if i < 137 then 119 else 120) else (if i < 139 then 121 else 121)) else (if i < 142 then (if i < 141 then 139 else 118) else (if i < 143 then 124 else 139)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 138 else 142) else (if i < 147 then 121 else 118)) else (if i < 150 then (if i < 149 then 181 else 186) else (if i < 151 then 3 else 187))) else (if i < 156 then (if i < 154 then (if i < 153 then 150 else 3) else (if i < 155 then 153 else 150)) else (if i < 158 then (if i < 157 then 152 else 152) else (if i < 159 then 3 else 152)))))

private def parentValue_b5 (i : ℕ) : ℕ :=
  (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 150 else 155) else (if i < 163 then 152 else 165)) else (if i < 166 then (if i < 165 then 153 else 153) else (if i < 167 then 165 else 161))) else (if i < 172 then (if i < 170 then (if i < 169 then 165 else 152) else (if i < 171 then 153 else 154)) else (if i < 174 then (if i < 173 then 154 else 172) else (if i < 175 then 151 else 151)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 172 else 171) else (if i < 179 then 175 else 154)) else (if i < 182 then (if i < 181 then 151 else 187) else (if i < 183 then 120 else 4))) else (if i < 188 then (if i < 186 then (if i < 185 then 121 else 183) else (if i < 187 then 4 else 186)) else (if i < 190 then (if i < 189 then 183 else 185) else (if i < 191 then 185 else 4)))))

private def parentValue_b6 (i : ℕ) : ℕ :=
  (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 185 else 183) else (if i < 195 then 188 else 185)) else (if i < 198 then (if i < 197 then 198 else 186) else (if i < 199 then 186 else 198))) else (if i < 204 then (if i < 202 then (if i < 201 then 194 else 198) else (if i < 203 then 185 else 186)) else (if i < 206 then (if i < 205 then 187 else 187) else (if i < 207 then 205 else 184)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 184 else 205) else (if i < 211 then 204 else 208)) else (if i < 214 then (if i < 213 then 187 else 184) else (if i < 215 then 153 else 186))) else (if i < 220 then (if i < 218 then (if i < 217 then 120 else 283) else (if i < 219 then 255 else 224)) else (if i < 222 then (if i < 221 then 217 else 220) else (if i < 223 then 284 else 286)))))

private def parentValue_b7 (i : ℕ) : ℕ :=
  (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 222 else 223) else (if i < 227 then 223 else 222)) else (if i < 230 then (if i < 229 then 223 else 220) else (if i < 231 then 224 else 221))) else (if i < 236 then (if i < 234 then (if i < 233 then 234 else 222) else (if i < 235 then 222 else 234)) else (if i < 238 then (if i < 237 then 230 else 234) else (if i < 239 then 221 else 222)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 223 else 217) else (if i < 243 then 241 else 217)) else (if i < 246 then (if i < 245 then 220 else 241) else (if i < 247 then 241 else 243))) else (if i < 252 then (if i < 250 then (if i < 249 then 241 else 243) else (if i < 251 then 283 else 18)) else (if i < 254 then (if i < 253 then 251 else 251) else (if i < 255 then 253 else 5)))))

private def parentValue_b8 (i : ℕ) : ℕ :=
  (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 258 else 252) else (if i < 259 then 254 else 254)) else (if i < 262 then (if i < 261 then 252 else 254) else (if i < 263 then 251 else 254))) else (if i < 268 then (if i < 266 then (if i < 265 then 254 else 264) else (if i < 267 then 258 else 257)) else (if i < 270 then (if i < 269 then 264 else 263) else (if i < 271 then 267 else 254)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 255 else 259) else (if i < 275 then 250 else 277)) else (if i < 278 then (if i < 277 then 253 else 253) else (if i < 279 then 277 else 275))) else (if i < 284 then (if i < 282 then (if i < 281 then 277 else 274) else (if i < 283 then 253 else 289)) else (if i < 286 then (if i < 285 then 285 else 4) else (if i < 287 then 287 else 285)))))

private def parentValue_b9 (i : ℕ) : ℕ :=
  (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 80 else 288) else (if i < 291 then 288 else 299)) else (if i < 294 then (if i < 293 then 289 else 288) else (if i < 295 then 289 else 285))) else (if i < 300 then (if i < 298 then (if i < 297 then 290 else 298) else (if i < 299 then 300 else 288)) else (if i < 302 then (if i < 301 then 288 else 300) else (if i < 303 then 296 else 300)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 296 else 288) else (if i < 307 then 289 else 289)) else (if i < 310 then (if i < 309 then 307 else 283) else (if i < 311 then 292 else 307))) else (if i < 316 then (if i < 314 then (if i < 313 then 306 else 310) else (if i < 315 then 289 else 310)) else (if i < 318 then (if i < 317 then 255 else 288) else (if i < 319 then 284 else 322)))))

private def parentValue_b10 (i : ℕ) : ℕ :=
  (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 357 else 320) else (if i < 323 then 358 else 322)) else (if i < 326 then (if i < 325 then 7 else 327) else (if i < 327 then 321 else 323))) else (if i < 332 then (if i < 330 then (if i < 329 then 323 else 321) else (if i < 331 then 323 else 320)) else (if i < 334 then (if i < 333 then 323 else 323) else (if i < 335 then 333 else 327)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 326 else 333) else (if i < 339 then 332 else 336)) else (if i < 342 then (if i < 341 then 323 else 324) else (if i < 343 then 328 else 319))) else (if i < 348 then (if i < 346 then (if i < 345 then 346 else 322) else (if i < 347 then 322 else 346)) else (if i < 350 then (if i < 349 then 344 else 346) else (if i < 351 then 343 else 322)))))

private def parentValue_b11 (i : ℕ) : ℕ :=
  (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 376 else 354) else (if i < 355 then 4 else 356)) else (if i < 358 then (if i < 357 then 354 else 4) else (if i < 359 then 357 else 354))) else (if i < 364 then (if i < 362 then (if i < 361 then 356 else 356) else (if i < 363 then 4 else 356)) else (if i < 366 then (if i < 365 then 354 else 359) else (if i < 367 then 356 else 369)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 357 else 357) else (if i < 371 then 369 else 365)) else (if i < 374 then (if i < 373 then 369 else 356) else (if i < 375 then 357 else 358))) else (if i < 380 then (if i < 378 then (if i < 377 then 358 else 376) else (if i < 379 then 355 else 361)) else (if i < 382 then (if i < 381 then 376 else 375) else (if i < 383 then 379 else 358)))))

private def parentValue_b12 (i : ℕ) : ℕ :=
  (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 355 else 391) else (if i < 387 then 387 else 5)) else (if i < 390 then (if i < 389 then 389 else 387) else (if i < 391 then 353 else 355))) else (if i < 396 then (if i < 394 then (if i < 393 then 390 else 391) else (if i < 395 then 391 else 5)) else (if i < 398 then (if i < 397 then 391 else 387) else (if i < 399 then 392 else 389)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 402 else 390) else (if i < 403 then 390 else 402)) else (if i < 406 then (if i < 405 then 398 else 402) else (if i < 407 then 389 else 390))) else (if i < 412 then (if i < 410 then (if i < 409 then 391 else 391) else (if i < 411 then 409 else 385)) else (if i < 414 then (if i < 413 then 394 else 409) else (if i < 415 then 408 else 412)))))

private def parentValue_b13 (i : ℕ) : ℕ :=
  (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 391 else 388) else (if i < 419 then 357 else 353)) else (if i < 422 then (if i < 421 then 386 else 424) else (if i < 423 then 459 else 7))) else (if i < 428 then (if i < 426 then (if i < 425 then 460 else 423) else (if i < 427 then 7 else 426)) else (if i < 430 then (if i < 429 then 423 else 425) else (if i < 431 then 425 else 7)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 425 else 422) else (if i < 435 then 428 else 425)) else (if i < 438 then (if i < 437 then 438 else 426) else (if i < 439 then 426 else 438))) else (if i < 444 then (if i < 442 then (if i < 441 then 434 else 438) else (if i < 443 then 425 else 426)) else (if i < 446 then (if i < 445 then 427 else 427) else (if i < 447 then 448 else 424)))))

private def parentValue_b14 (i : ℕ) : ℕ :=
  (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 424 else 448) else (if i < 451 then 444 else 448)) else (if i < 454 then (if i < 453 then 427 else 424) else (if i < 455 then 478 else 255))) else (if i < 460 then (if i < 458 then (if i < 457 then 5 else 455) else (if i < 459 then 456 else 5)) else (if i < 462 then (if i < 461 then 459 else 456) else (if i < 463 then 458 else 458)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 5 else 458) else (if i < 467 then 456 else 461)) else (if i < 470 then (if i < 469 then 458 else 471) else (if i < 471 then 459 else 459))) else (if i < 476 then (if i < 474 then (if i < 473 then 471 else 467) else (if i < 475 then 471 else 458)) else (if i < 478 then (if i < 477 then 459 else 460) else (if i < 479 then 460 else 478)))))

private def parentValue_b15 (i : ℕ) : ℕ :=
  (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 457 else 457) else (if i < 483 then 478 else 477)) else (if i < 486 then (if i < 485 then 481 else 460) else (if i < 487 then 457 else 493))) else (if i < 492 then (if i < 490 then (if i < 489 then 489 else 6) else (if i < 491 then 491 else 489)) else (if i < 494 then (if i < 493 then 6 else 492) else (if i < 495 then 489 else 491)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 491 else 6) else (if i < 499 then 491 else 489)) else (if i < 502 then (if i < 501 then 494 else 491) else (if i < 503 then 504 else 492))) else (if i < 508 then (if i < 506 then (if i < 505 then 492 else 504) else (if i < 507 then 500 else 504)) else (if i < 510 then (if i < 509 then 491 else 492) else (if i < 511 then 493 else 493)))))

private def parentValue_b16 (i : ℕ) : ℕ :=
  (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 511 else 490) else (if i < 515 then 496 else 511)) else (if i < 518 then (if i < 517 then 510 else 514) else (if i < 519 then 493 else 490))) else (if i < 524 then (if i < 522 then (if i < 521 then 459 else 455) else (if i < 523 then 426 else 589)) else (if i < 526 then (if i < 525 then 525 else 530) else (if i < 527 then 523 else 525)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 47 else 528) else (if i < 531 then 528 else 539)) else (if i < 534 then (if i < 533 then 529 else 528) else (if i < 535 then 529 else 525))) else (if i < 540 then (if i < 538 then (if i < 537 then 530 else 538) else (if i < 539 then 540 else 528)) else (if i < 542 then (if i < 541 then 528 else 540) else (if i < 543 then 536 else 540)))))

private def parentValue_b17 (i : ℕ) : ℕ :=
  (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then 536 else 528) else (if i < 547 then 529 else 529)) else (if i < 550 then (if i < 549 then 547 else 523) else (if i < 551 then 532 else 547))) else (if i < 556 then (if i < 554 then (if i < 553 then 546 else 549) else (if i < 555 then 529 else 549)) else (if i < 558 then (if i < 557 then 589 else 594) else (if i < 559 then 557 else 595)))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then 559 else 8) else (if i < 563 then 564 else 558)) else (if i < 566 then (if i < 565 then 560 else 560) else (if i < 567 then 558 else 560))) else (if i < 572 then (if i < 570 then (if i < 569 then 557 else 560) else (if i < 571 then 560 else 570)) else (if i < 574 then (if i < 573 then 564 else 563) else (if i < 575 then 570 else 569)))))

private def parentValue_b18 (i : ℕ) : ℕ :=
  (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then 573 else 560) else (if i < 579 then 561 else 565)) else (if i < 582 then (if i < 581 then 556 else 583) else (if i < 583 then 559 else 559))) else (if i < 588 then (if i < 586 then (if i < 585 then 583 else 581) else (if i < 587 then 583 else 580)) else (if i < 590 then (if i < 589 then 559 else 595) else (if i < 591 then 84 else 0)))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then 590 else 591) else (if i < 595 then 0 else 594)) else (if i < 598 then (if i < 597 then 591 else 593) else (if i < 599 then 593 else 0))) else (if i < 604 then (if i < 602 then (if i < 601 then 593 else 591) else (if i < 603 then 596 else 593)) else (if i < 606 then (if i < 605 then 606 else 594) else (if i < 607 then 594 else 606)))))

private def parentValue_b19 (i : ℕ) : ℕ :=
  (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then 602 else 606) else (if i < 611 then 593 else 594)) else (if i < 614 then (if i < 613 then 595 else 595) else (if i < 615 then 613 else 592))) else (if i < 620 then (if i < 618 then (if i < 617 then 592 else 613) else (if i < 619 then 612 else 616)) else (if i < 622 then (if i < 621 then 595 else 592) else (if i < 623 then 526 else 594)))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then 590 else 628) else (if i < 627 then 627 else 9)) else (if i < 630 then (if i < 629 then 629 else 627) else (if i < 631 then 9 else 630))) else (if i < 636 then (if i < 634 then (if i < 633 then 627 else 629) else (if i < 635 then 629 else 9)) else (if i < 638 then (if i < 637 then 629 else 627) else (if i < 639 then 632 else 629)))))

private def parentValue_b20 (i : ℕ) : ℕ :=
  (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then 642 else 630) else (if i < 643 then 630 else 642)) else (if i < 646 then (if i < 645 then 638 else 642) else (if i < 647 then 629 else 630))) else (if i < 652 then (if i < 650 then (if i < 649 then 631 else 631) else (if i < 651 then 649 else 628)) else (if i < 654 then (if i < 653 then 634 else 649) else (if i < 655 then 648 else 652)))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then 631 else 628) else (if i < 659 then 691 else 696)) else (if i < 662 then (if i < 661 then 659 else 697) else (if i < 663 then 661 else 626))) else (if i < 668 then (if i < 666 then (if i < 665 then 628 else 663) else (if i < 667 then 664 else 664)) else (if i < 670 then (if i < 669 then 2 else 664) else (if i < 671 then 659 else 665)))))

private def parentValue_b21 (i : ℕ) : ℕ :=
  (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then 662 else 675) else (if i < 675 then 663 else 663)) else (if i < 678 then (if i < 677 then 675 else 671) else (if i < 679 then 675 else 662))) else (if i < 684 then (if i < 682 then (if i < 681 then 663 else 664) else (if i < 683 then 664 else 685)) else (if i < 686 then (if i < 685 then 661 else 661) else (if i < 687 then 685 else 681)))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then 685 else 664) else (if i < 691 then 661 else 697)) else (if i < 694 then (if i < 693 then 630 else 8) else (if i < 695 then 631 else 693))) else (if i < 700 then (if i < 698 then (if i < 697 then 8 else 696) else (if i < 699 then 693 else 695)) else (if i < 702 then (if i < 701 then 695 else 8) else (if i < 703 then 695 else 693)))))

private def parentValue_b22 (i : ℕ) : ℕ :=
  (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then 698 else 695) else (if i < 707 then 708 else 696)) else (if i < 710 then (if i < 709 then 696 else 708) else (if i < 711 then 704 else 708))) else (if i < 716 then (if i < 714 then (if i < 713 then 695 else 696) else (if i < 715 then 697 else 697)) else (if i < 718 then (if i < 717 then 715 else 694) else (if i < 719 then 694 else 715)))) else (if i < 728 then (if i < 724 then (if i < 722 then (if i < 721 then 714 else 718) else (if i < 723 then 697 else 694)) else (if i < 726 then (if i < 725 then 626 else 696) else (if i < 727 then 630 else 793))) else (if i < 732 then (if i < 730 then (if i < 729 then 729 else 734) else (if i < 731 then 727 else 736)) else (if i < 734 then (if i < 733 then 794 else 796) else (if i < 735 then 732 else 733)))))

private def parentValue_b23 (i : ℕ) : ℕ :=
  (if i < 752 then (if i < 744 then (if i < 740 then (if i < 738 then (if i < 737 then 733 else 732) else (if i < 739 then 733 else 729)) else (if i < 742 then (if i < 741 then 734 else 735) else (if i < 743 then 744 else 732))) else (if i < 748 then (if i < 746 then (if i < 745 then 732 else 744) else (if i < 747 then 740 else 744)) else (if i < 750 then (if i < 749 then 740 else 732) else (if i < 751 then 733 else 733)))) else (if i < 760 then (if i < 756 then (if i < 754 then (if i < 753 then 751 else 727) else (if i < 755 then 736 else 751)) else (if i < 758 then (if i < 757 then 750 else 753) else (if i < 759 then 733 else 753))) else (if i < 764 then (if i < 762 then (if i < 761 then 793 else 798) else (if i < 763 then 761 else 799)) else (if i < 766 then (if i < 765 then 763 else 10) else (if i < 767 then 768 else 762)))))

private def parentValue_b24 (i : ℕ) : ℕ :=
  (if i < 784 then (if i < 776 then (if i < 772 then (if i < 770 then (if i < 769 then 764 else 764) else (if i < 771 then 762 else 764)) else (if i < 774 then (if i < 773 then 761 else 764) else (if i < 775 then 764 else 774))) else (if i < 780 then (if i < 778 then (if i < 777 then 768 else 767) else (if i < 779 then 774 else 773)) else (if i < 782 then (if i < 781 then 777 else 764) else (if i < 783 then 765 else 769)))) else (if i < 792 then (if i < 788 then (if i < 786 then (if i < 785 then 760 else 787) else (if i < 787 then 763 else 763)) else (if i < 790 then (if i < 789 then 787 else 785) else (if i < 791 then 787 else 784))) else (if i < 796 then (if i < 794 then (if i < 793 then 763 else 799) else (if i < 795 then 795 else 9)) else (if i < 798 then (if i < 797 then 797 else 795) else (if i < 799 then 9 else 798)))))

private def parentValue_b25 (i : ℕ) : ℕ :=
  (if i < 816 then (if i < 808 then (if i < 804 then (if i < 802 then (if i < 801 then 795 else 797) else (if i < 803 then 797 else 9)) else (if i < 806 then (if i < 805 then 797 else 795) else (if i < 807 then 800 else 797))) else (if i < 812 then (if i < 810 then (if i < 809 then 810 else 798) else (if i < 811 then 798 else 810)) else (if i < 814 then (if i < 813 then 806 else 810) else (if i < 815 then 797 else 798)))) else (if i < 824 then (if i < 820 then (if i < 818 then (if i < 817 then 799 else 799) else (if i < 819 then 817 else 796)) else (if i < 822 then (if i < 821 then 802 else 817) else (if i < 823 then 816 else 820))) else (if i < 828 then (if i < 826 then (if i < 825 then 799 else 796) else (if i < 827 then 730 else 798)) else (if i < 830 then (if i < 829 then 794 else 895) else (if i < 831 then 831 else 10)))))

private def parentValue_b26 (i : ℕ) : ℕ :=
  (if i < 848 then (if i < 840 then (if i < 836 then (if i < 834 then (if i < 833 then 829 else 831) else (if i < 835 then 896 else 898)) else (if i < 838 then (if i < 837 then 834 else 835) else (if i < 839 then 835 else 834))) else (if i < 844 then (if i < 842 then (if i < 841 then 835 else 831) else (if i < 843 then 836 else 837)) else (if i < 846 then (if i < 845 then 846 else 834) else (if i < 847 then 834 else 846)))) else (if i < 856 then (if i < 852 then (if i < 850 then (if i < 849 then 842 else 846) else (if i < 851 then 842 else 834)) else (if i < 854 then (if i < 853 then 835 else 835) else (if i < 855 then 853 else 829))) else (if i < 860 then (if i < 858 then (if i < 857 then 838 else 853) else (if i < 859 then 852 else 855)) else (if i < 862 then (if i < 861 then 835 else 855) else (if i < 863 then 895 else 900)))))

private def parentValue_b27 (i : ℕ) : ℕ :=
  (if i < 880 then (if i < 872 then (if i < 868 then (if i < 866 then (if i < 865 then 863 else 901) else (if i < 867 then 865 else 12)) else (if i < 870 then (if i < 869 then 870 else 864) else (if i < 871 then 866 else 866))) else (if i < 876 then (if i < 874 then (if i < 873 then 864 else 866) else (if i < 875 then 863 else 866)) else (if i < 878 then (if i < 877 then 866 else 876) else (if i < 879 then 870 else 869)))) else (if i < 888 then (if i < 884 then (if i < 882 then (if i < 881 then 876 else 875) else (if i < 883 then 879 else 866)) else (if i < 886 then (if i < 885 then 867 else 871) else (if i < 887 then 862 else 889))) else (if i < 892 then (if i < 890 then (if i < 889 then 865 else 865) else (if i < 891 then 889 else 887)) else (if i < 894 then (if i < 893 then 889 else 886) else (if i < 895 then 865 else 901)))))

private def parentValue_b28 (i : ℕ) : ℕ :=
  (if i < 912 then (if i < 904 then (if i < 900 then (if i < 898 then (if i < 897 then 897 else 9) else (if i < 899 then 899 else 897)) else (if i < 902 then (if i < 901 then 9 else 900) else (if i < 903 then 897 else 899))) else (if i < 908 then (if i < 906 then (if i < 905 then 899 else 9) else (if i < 907 then 899 else 897)) else (if i < 910 then (if i < 909 then 902 else 899) else (if i < 911 then 912 else 900)))) else (if i < 920 then (if i < 916 then (if i < 914 then (if i < 913 then 900 else 912) else (if i < 915 then 908 else 912)) else (if i < 918 then (if i < 917 then 899 else 900) else (if i < 919 then 901 else 901))) else (if i < 924 then (if i < 922 then (if i < 921 then 919 else 898) else (if i < 923 then 904 else 919)) else (if i < 926 then (if i < 925 then 918 else 922) else (if i < 927 then 901 else 898)))))

private def parentValue_b29 (i : ℕ) : ℕ :=
  (if i < 944 then (if i < 936 then (if i < 932 then (if i < 930 then (if i < 929 then 832 else 900) else (if i < 931 then 896 else 997)) else (if i < 934 then (if i < 933 then 969 else 12) else (if i < 935 then 970 else 933))) else (if i < 940 then (if i < 938 then (if i < 937 then 12 else 936) else (if i < 939 then 933 else 935)) else (if i < 942 then (if i < 941 then 935 else 12) else (if i < 943 then 935 else 933)))) else (if i < 952 then (if i < 948 then (if i < 946 then (if i < 945 then 938 else 935) else (if i < 947 then 948 else 936)) else (if i < 950 then (if i < 949 then 936 else 948) else (if i < 951 then 944 else 948))) else (if i < 956 then (if i < 954 then (if i < 953 then 935 else 936) else (if i < 955 then 937 else 937)) else (if i < 958 then (if i < 957 then 955 else 934) else (if i < 959 then 934 else 955)))))

private def parentValue_b30 (i : ℕ) : ℕ :=
  (if i < 976 then (if i < 968 then (if i < 964 then (if i < 962 then (if i < 961 then 954 else 958) else (if i < 963 then 937 else 934)) else (if i < 966 then (if i < 965 then 997 else 1002) else (if i < 967 then 10 else 1003))) else (if i < 972 then (if i < 970 then (if i < 969 then 966 else 10) else (if i < 971 then 969 else 966)) else (if i < 974 then (if i < 973 then 968 else 968) else (if i < 975 then 10 else 968)))) else (if i < 984 then (if i < 980 then (if i < 978 then (if i < 977 then 966 else 971) else (if i < 979 then 968 else 981)) else (if i < 982 then (if i < 981 then 969 else 969) else (if i < 983 then 981 else 977))) else (if i < 988 then (if i < 986 then (if i < 985 then 981 else 968) else (if i < 987 then 969 else 970)) else (if i < 990 then (if i < 989 then 970 else 988) else (if i < 991 then 967 else 967)))))

private def parentValue_b31 (i : ℕ) : ℕ :=
  (if i < 1008 then (if i < 1000 then (if i < 996 then (if i < 994 then (if i < 993 then 988 else 987) else (if i < 995 then 991 else 970)) else (if i < 998 then (if i < 997 then 967 else 1003) else (if i < 999 then 999 else 11))) else (if i < 1004 then (if i < 1002 then (if i < 1001 then 1001 else 999) else (if i < 1003 then 11 else 1002)) else (if i < 1006 then (if i < 1005 then 999 else 1001) else (if i < 1007 then 1001 else 11)))) else (if i < 1016 then (if i < 1012 then (if i < 1010 then (if i < 1009 then 1001 else 999) else (if i < 1011 then 1004 else 1001)) else (if i < 1014 then (if i < 1013 then 1014 else 1002) else (if i < 1015 then 1002 else 1014))) else (if i < 1020 then (if i < 1018 then (if i < 1017 then 1010 else 1014) else (if i < 1019 then 1001 else 1002)) else (if i < 1022 then (if i < 1021 then 1003 else 1003) else (if i < 1023 then 1021 else 1000)))))

private def parentValue_b32 (i : ℕ) : ℕ :=
  (if i < 1040 then (if i < 1032 then (if i < 1028 then (if i < 1026 then (if i < 1025 then 1006 else 1021) else (if i < 1027 then 1020 else 1024)) else (if i < 1030 then (if i < 1029 then 1003 else 1000) else (if i < 1031 then 969 else 1002))) else (if i < 1036 then (if i < 1034 then (if i < 1033 then 936 else 1034) else (if i < 1035 then 0 else 1036)) else (if i < 1038 then (if i < 1037 then 1 else 1057) else (if i < 1039 then 1037 else 594)))) else (if i < 1048 then (if i < 1044 then (if i < 1042 then (if i < 1041 then 557 else 594) else (if i < 1043 then 1034 else 1036)) else (if i < 1046 then (if i < 1045 then 696 else 186) else (if i < 1047 then 80 else 84))) else (if i < 1052 then (if i < 1050 then (if i < 1049 then 357 else 255) else (if i < 1051 then 630 else 798)) else (if i < 1054 then (if i < 1053 then 900 else 1002) else (if i < 1055 then 1033 else 0)))))

private def parentValue_b33 (i : ℕ) : ℕ :=
  (if i < 1057 then 1055 else 1054)

private def parentValue_n0_0 (i : ℕ) : ℕ := if i < 32 then parentValue_b0 i else parentValue_b1 i

private def parentValue_n0_1 (i : ℕ) : ℕ := if i < 96 then parentValue_b2 i else parentValue_b3 i

private def parentValue_n0_2 (i : ℕ) : ℕ := if i < 160 then parentValue_b4 i else parentValue_b5 i

private def parentValue_n0_3 (i : ℕ) : ℕ := if i < 224 then parentValue_b6 i else parentValue_b7 i

private def parentValue_n0_4 (i : ℕ) : ℕ := if i < 288 then parentValue_b8 i else parentValue_b9 i

private def parentValue_n0_5 (i : ℕ) : ℕ := if i < 352 then parentValue_b10 i else parentValue_b11 i

private def parentValue_n0_6 (i : ℕ) : ℕ := if i < 416 then parentValue_b12 i else parentValue_b13 i

private def parentValue_n0_7 (i : ℕ) : ℕ := if i < 480 then parentValue_b14 i else parentValue_b15 i

private def parentValue_n0_8 (i : ℕ) : ℕ := if i < 544 then parentValue_b16 i else parentValue_b17 i

private def parentValue_n0_9 (i : ℕ) : ℕ := if i < 608 then parentValue_b18 i else parentValue_b19 i

private def parentValue_n0_10 (i : ℕ) : ℕ := if i < 672 then parentValue_b20 i else parentValue_b21 i

private def parentValue_n0_11 (i : ℕ) : ℕ := if i < 736 then parentValue_b22 i else parentValue_b23 i

private def parentValue_n0_12 (i : ℕ) : ℕ := if i < 800 then parentValue_b24 i else parentValue_b25 i

private def parentValue_n0_13 (i : ℕ) : ℕ := if i < 864 then parentValue_b26 i else parentValue_b27 i

private def parentValue_n0_14 (i : ℕ) : ℕ := if i < 928 then parentValue_b28 i else parentValue_b29 i

private def parentValue_n0_15 (i : ℕ) : ℕ := if i < 992 then parentValue_b30 i else parentValue_b31 i

private def parentValue_n0_16 (i : ℕ) : ℕ := if i < 1056 then parentValue_b32 i else parentValue_b33 i

private def parentValue_n1_0 (i : ℕ) : ℕ := if i < 64 then parentValue_n0_0 i else parentValue_n0_1 i

private def parentValue_n1_1 (i : ℕ) : ℕ := if i < 192 then parentValue_n0_2 i else parentValue_n0_3 i

private def parentValue_n1_2 (i : ℕ) : ℕ := if i < 320 then parentValue_n0_4 i else parentValue_n0_5 i

private def parentValue_n1_3 (i : ℕ) : ℕ := if i < 448 then parentValue_n0_6 i else parentValue_n0_7 i

private def parentValue_n1_4 (i : ℕ) : ℕ := if i < 576 then parentValue_n0_8 i else parentValue_n0_9 i

private def parentValue_n1_5 (i : ℕ) : ℕ := if i < 704 then parentValue_n0_10 i else parentValue_n0_11 i

private def parentValue_n1_6 (i : ℕ) : ℕ := if i < 832 then parentValue_n0_12 i else parentValue_n0_13 i

private def parentValue_n1_7 (i : ℕ) : ℕ := if i < 960 then parentValue_n0_14 i else parentValue_n0_15 i

private def parentValue_n2_0 (i : ℕ) : ℕ := if i < 128 then parentValue_n1_0 i else parentValue_n1_1 i

private def parentValue_n2_1 (i : ℕ) : ℕ := if i < 384 then parentValue_n1_2 i else parentValue_n1_3 i

private def parentValue_n2_2 (i : ℕ) : ℕ := if i < 640 then parentValue_n1_4 i else parentValue_n1_5 i

private def parentValue_n2_3 (i : ℕ) : ℕ := if i < 896 then parentValue_n1_6 i else parentValue_n1_7 i

private def parentValue_n3_0 (i : ℕ) : ℕ := if i < 256 then parentValue_n2_0 i else parentValue_n2_1 i

private def parentValue_n3_1 (i : ℕ) : ℕ := if i < 768 then parentValue_n2_2 i else parentValue_n2_3 i

private def parentValue_n4_0 (i : ℕ) : ℕ := if i < 512 then parentValue_n3_0 i else parentValue_n3_1 i

private def parentValue_n5_0 (i : ℕ) : ℕ := if i < 1024 then parentValue_n4_0 i else parentValue_n0_16 i

def parentValue (i : ℕ) : ℕ := parentValue_n5_0 i

end PlanarHom.ColoringMacroFaces.FanFramed
