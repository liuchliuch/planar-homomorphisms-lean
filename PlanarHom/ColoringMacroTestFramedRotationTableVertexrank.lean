import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.TestFramed
private def vertexRankValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 4 else 2) else (if i < 3 then 4 else 1)) else (if i < 6 then (if i < 5 then 3 else 1) else (if i < 7 then 3 else 2))) else (if i < 12 then (if i < 10 then (if i < 9 then 3 else 1) else (if i < 11 then 3 else 0)) else (if i < 14 then (if i < 13 then 2 else 3) else (if i < 15 then 2 else 2)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 1 else 6) else (if i < 19 then 8 else 2)) else (if i < 22 then (if i < 21 then 4 else 4) else (if i < 23 then 6 else 4))) else (if i < 28 then (if i < 26 then (if i < 25 then 0 else 2) else (if i < 27 then 7 else 1)) else (if i < 30 then (if i < 29 then 3 else 0) else (if i < 31 then 5 else 3)))))

private def vertexRankValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 5 else 3) else (if i < 35 then 5 else 0)) else (if i < 38 then (if i < 37 then 2 else 5) else (if i < 39 then 1 else 3))) else (if i < 44 then (if i < 42 then (if i < 41 then 4 else 1) else (if i < 43 then 4 else 0)) else (if i < 46 then (if i < 45 then 1 else 3) else (if i < 47 then 0 else 2)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 1 else 2) else (if i < 51 then 0 else 3)) else (if i < 54 then (if i < 53 then 5 else 0) else (if i < 55 then 2 else 3))) else (if i < 60 then (if i < 58 then (if i < 57 then 0 else 2) else (if i < 59 then 3 else 1)) else (if i < 62 then (if i < 61 then 4 else 0) else (if i < 63 then 1 else 3)))))

private def vertexRankValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0 else 2) else (if i < 67 then 4 else 1)) else (if i < 70 then (if i < 69 then 3 else 1) else (if i < 71 then 3 else 9))) else (if i < 76 then (if i < 74 then (if i < 73 then 10 else 2) else (if i < 75 then 3 else 1)) else (if i < 78 then (if i < 77 then 2 else 0) else (if i < 79 then 2 else 3)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0 else 1) else (if i < 83 then 4 else 1)) else (if i < 86 then (if i < 85 then 2 else 0) else (if i < 87 then 2 else 3))) else (if i < 92 then (if i < 90 then (if i < 89 then 1 else 0) else (if i < 91 then 4 else 0)) else (if i < 94 then (if i < 93 then 5 else 1) else (if i < 95 then 2 else 0)))))

private def vertexRankValue_b3 (i : ℕ) : ℕ :=
  (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0 else 3) else (if i < 99 then 5 else 2)) else (if i < 102 then (if i < 101 then 2 else 1) else (if i < 103 then 3 else 3))) else (if i < 108 then (if i < 106 then (if i < 105 then 1 else 5) else (if i < 107 then 3 else 0)) else (if i < 110 then (if i < 109 then 3 else 2) else (if i < 111 then 0 else 3)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 2 else 0) else (if i < 115 then 4 else 1)) else (if i < 118 then (if i < 117 then 6 else 1) else (if i < 119 then 5 else 2))) else (if i < 124 then (if i < 122 then (if i < 121 then 0 else 3) else (if i < 123 then 1 else 8)) else (if i < 126 then (if i < 125 then 7 else 1) else (if i < 127 then 0 else 2)))))

private def vertexRankValue_b4 (i : ℕ) : ℕ :=
  (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 1 else 3) else (if i < 131 then 2 else 0)) else (if i < 134 then (if i < 133 then 0 else 2) else (if i < 135 then 1 else 2))) else (if i < 140 then (if i < 138 then (if i < 137 then 1 else 2) else (if i < 139 then 0 else 2)) else (if i < 142 then (if i < 141 then 1 else 3) else (if i < 143 then 1 else 2)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 4 else 1) else (if i < 147 then 0 else 3)) else (if i < 150 then (if i < 149 then 0 else 2) else (if i < 151 then 0 else 3))) else (if i < 156 then (if i < 154 then (if i < 153 then 4 else 1) else (if i < 155 then 3 else 0)) else (if i < 158 then (if i < 157 then 2 else 0) else (if i < 159 then 2 else 2)))))

private def vertexRankValue_b5 (i : ℕ) : ℕ :=
  (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 3 else 1) else (if i < 163 then 2 else 0)) else (if i < 166 then (if i < 165 then 1 else 3) else (if i < 167 then 1 else 2))) else (if i < 172 then (if i < 170 then (if i < 169 then 0 else 5) else (if i < 171 then 7 else 1)) else (if i < 174 then (if i < 173 then 3 else 8) else (if i < 175 then 1 else 3)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 4 else 1) else (if i < 179 then 6 else 0)) else (if i < 182 then (if i < 181 then 2 else 3) else (if i < 183 then 0 else 2))) else (if i < 188 then (if i < 186 then (if i < 185 then 5 else 1) else (if i < 187 then 3 else 8)) else (if i < 190 then (if i < 189 then 1 else 4) else (if i < 191 then 0 else 3)))))

private def vertexRankValue_b6 (i : ℕ) : ℕ :=
  (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 4 else 0) else (if i < 195 then 2 else 3)) else (if i < 198 then (if i < 197 then 0 else 2) else (if i < 199 then 5 else 1))) else (if i < 204 then (if i < 202 then (if i < 201 then 0 else 2) else (if i < 203 then 0 else 2)) else (if i < 206 then (if i < 205 then 4 else 5) else (if i < 207 then 1 else 2)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 3 else 2) else (if i < 211 then 3 else 1)) else (if i < 214 then (if i < 213 then 3 else 0) else (if i < 215 then 0 else 3))) else (if i < 220 then (if i < 218 then (if i < 217 then 10 else 1) else (if i < 219 then 3 else 0)) else (if i < 222 then (if i < 221 then 2 else 1) else (if i < 223 then 3 else 8)))))

private def vertexRankValue_b7 (i : ℕ) : ℕ :=
  (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 9 else 1) else (if i < 227 then 2 else 0)) else (if i < 230 then (if i < 229 then 1 else 3) else (if i < 231 then 2 else 2))) else (if i < 236 then (if i < 234 then (if i < 233 then 4 else 1) else (if i < 235 then 3 else 0)) else (if i < 238 then (if i < 237 then 1 else 0) else (if i < 239 then 2 else 2)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 1 else 5) else (if i < 243 then 3 else 0)) else (if i < 246 then (if i < 245 then 4 else 1) else (if i < 247 then 2 else 3))) else (if i < 252 then (if i < 250 then (if i < 249 then 0 else 2) else (if i < 251 then 4 else 1)) else (if i < 254 then (if i < 253 then 1 else 3) else (if i < 255 then 1 else 7)))))

private def vertexRankValue_b8 (i : ℕ) : ℕ :=
  (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 5 else 4) else (if i < 259 then 2 else 3)) else (if i < 262 then (if i < 261 then 2 else 0) else (if i < 263 then 2 else 1))) else (if i < 268 then (if i < 266 then (if i < 265 then 6 else 2) else (if i < 267 then 3 else 3)) else (if i < 270 then (if i < 269 then 4 else 0) else (if i < 271 then 4 else 1)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 3 else 2) else (if i < 275 then 0 else 6)) else (if i < 278 then (if i < 277 then 5 else 0) else (if i < 279 then 5 else 1))) else (if i < 284 then (if i < 282 then (if i < 281 then 0 else 2) else (if i < 283 then 1 else 3)) else (if i < 286 then (if i < 285 then 4 else 0) else (if i < 287 then 0 else 1)))))

private def vertexRankValue_b9 (i : ℕ) : ℕ :=
  (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 0 else 1) else (if i < 291 then 2 else 1)) else (if i < 294 then (if i < 293 then 0 else 2) else (if i < 295 then 0 else 2))) else (if i < 300 then (if i < 298 then (if i < 297 then 3 else 1) else (if i < 299 then 0 else 2)) else (if i < 302 then (if i < 301 then 3 else 0) else (if i < 303 then 5 else 1)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 4 else 3) else (if i < 307 then 5 else 2)) else (if i < 310 then (if i < 309 then 4 else 9) else (if i < 311 then 0 else 2))) else (if i < 316 then (if i < 314 then (if i < 313 then 3 else 2) else (if i < 315 then 4 else 1)) else (if i < 318 then (if i < 317 then 3 else 0) else (if i < 319 then 10 else 3)))))

private def vertexRankValue_b10 (i : ℕ) : ℕ :=
  (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 3 else 8) else (if i < 323 then 1 else 2)) else (if i < 326 then (if i < 325 then 4 else 6) else (if i < 327 then 8 else 1))) else (if i < 332 then (if i < 330 then (if i < 329 then 2 else 0) else (if i < 331 then 0 else 3)) else (if i < 334 then (if i < 333 then 3 else 2) else (if i < 335 then 7 else 1)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 6 else 4) else (if i < 339 then 6 else 2)) else (if i < 342 then (if i < 341 then 4 else 0) else (if i < 343 then 2 else 4))) else (if i < 348 then (if i < 346 then (if i < 345 then 5 else 2) else (if i < 347 then 5 else 1)) else (if i < 350 then (if i < 349 then 3 else 0) else (if i < 351 then 1 else 3)))))

private def vertexRankValue_b11 (i : ℕ) : ℕ :=
  (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 2 else 3) else (if i < 355 then 1 else 5)) else (if i < 358 then (if i < 357 then 7 else 2) else (if i < 359 then 4 else 0))) else (if i < 364 then (if i < 362 then (if i < 361 then 1 else 3) else (if i < 363 then 0 else 2)) else (if i < 366 then (if i < 365 then 6 else 1) else (if i < 367 then 3 else 0)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 8 else 4) else (if i < 371 then 0 else 2)) else (if i < 374 then (if i < 373 then 0 else 2) else (if i < 375 then 0 else 6))) else (if i < 380 then (if i < 378 then (if i < 377 then 7 else 0) else (if i < 379 then 5 else 3)) else (if i < 382 then (if i < 381 then 3 else 2) else (if i < 383 then 3 else 1)))))

private def vertexRankValue_b12 (i : ℕ) : ℕ :=
  (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 1 else 2) else (if i < 387 then 0 else 3)) else (if i < 390 then (if i < 389 then 3 else 2) else (if i < 391 then 1 else 5))) else (if i < 396 then (if i < 394 then (if i < 393 then 0 else 2) else (if i < 395 then 0 else 1)) else (if i < 398 then (if i < 397 then 1 else 2) else (if i < 399 then 0 else 1)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 1 else 0) else (if i < 403 then 1 else 4)) else (if i < 406 then (if i < 405 then 3 else 2) else (if i < 407 then 0 else 5))) else (if i < 412 then (if i < 410 then (if i < 409 then 3 else 0) else (if i < 411 then 4 else 1)) else (if i < 414 then (if i < 413 then 0 else 2) else (if i < 415 then 1 else 3)))))

private def vertexRankValue_b13 (i : ℕ) : ℕ :=
  (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 4 else 0) else (if i < 419 then 5 else 1)) else (if i < 422 then (if i < 421 then 7 else 4) else (if i < 423 then 2 else 3))) else (if i < 428 then (if i < 426 then (if i < 425 then 1 else 3) else (if i < 427 then 1 else 1)) else (if i < 430 then (if i < 429 then 0 else 2) else (if i < 431 then 3 else 3)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 2 else 0) else (if i < 435 then 2 else 1)) else (if i < 438 then (if i < 437 then 0 else 3) else (if i < 439 then 1 else 5))) else (if i < 444 then (if i < 442 then (if i < 441 then 2 else 0) else (if i < 443 then 1 else 3)) else (if i < 446 then (if i < 445 then 2 else 0) else (if i < 447 then 2 else 0)))))

private def vertexRankValue_b14 (i : ℕ) : ℕ :=
  (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 1 else 2) else (if i < 451 then 1 else 0)) else (if i < 454 then (if i < 453 then 0 else 3) else (if i < 455 then 1 else 4))) else (if i < 460 then (if i < 458 then (if i < 457 then 1 else 4) else (if i < 459 then 2 else 7)) else (if i < 462 then (if i < 461 then 5 else 0) else (if i < 463 then 6 else 2)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 2 else 3) else (if i < 467 then 3 else 0)) else (if i < 470 then (if i < 469 then 6 else 1) else (if i < 471 then 7 else 1))) else (if i < 476 then (if i < 474 then (if i < 473 then 9 else 5) else (if i < 475 then 3 else 0)) else (if i < 478 then (if i < 477 then 6 else 1) else (if i < 479 then 0 else 2)))))

private def vertexRankValue_b15 (i : ℕ) : ℕ :=
  (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 0 else 3) else (if i < 483 then 4 else 0)) else (if i < 486 then (if i < 485 then 2 else 0) else (if i < 487 then 7 else 8))) else (if i < 492 then (if i < 490 then (if i < 489 then 6 else 1) else (if i < 491 then 0 else 2)) else (if i < 494 then (if i < 493 then 3 else 3) else (if i < 495 then 8 else 0)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 7 else 1) else (if i < 499 then 0 else 2)) else (if i < 502 then (if i < 501 then 3 else 1) else (if i < 503 then 2 else 4))) else (if i < 508 then (if i < 506 then (if i < 505 then 1 else 0) else (if i < 507 then 0 else 2)) else (if i < 510 then (if i < 509 then 1 else 3) else (if i < 511 then 2 else 2)))))

private def vertexRankValue_b16 (i : ℕ) : ℕ :=
  (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 1 else 3) else (if i < 515 then 2 else 0)) else (if i < 518 then (if i < 517 then 2 else 1) else (if i < 519 then 3 else 2))) else (if i < 524 then (if i < 522 then (if i < 521 then 3 else 3) else (if i < 523 then 2 else 2)) else (if i < 526 then (if i < 525 then 1 else 3) else (if i < 527 then 4 else 0)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 2 else 1) else (if i < 531 then 3 else 2)) else (if i < 534 then (if i < 533 then 4 else 3) else (if i < 535 then 2 else 3))) else (if i < 540 then (if i < 538 then (if i < 537 then 2 else 3) else (if i < 539 then 5 else 0)) else (if i < 542 then (if i < 541 then 2 else 1) else (if i < 543 then 3 else 2)))))

private def vertexRankValue_b17 (i : ℕ) : ℕ :=
  (if i < 557 then (if i < 550 then (if i < 547 then (if i < 545 then 1 else (if i < 546 then 0 else 1)) else (if i < 548 then 0 else (if i < 549 then 1 else 0))) else (if i < 553 then (if i < 551 then 1 else (if i < 552 then 0 else 1)) else (if i < 555 then (if i < 554 then 0 else 1) else (if i < 556 then 0 else 1)))) else (if i < 563 then (if i < 560 then (if i < 558 then 0 else (if i < 559 then 1 else 0)) else (if i < 561 then 1 else (if i < 562 then 0 else 1))) else (if i < 566 then (if i < 564 then 0 else (if i < 565 then 1 else 1)) else (if i < 568 then (if i < 567 then 0 else 0) else (if i < 569 then 1 else 0)))))

private def vertexRankValue_n0_0 (i : ℕ) : ℕ := if i < 32 then vertexRankValue_b0 i else vertexRankValue_b1 i

private def vertexRankValue_n0_1 (i : ℕ) : ℕ := if i < 96 then vertexRankValue_b2 i else vertexRankValue_b3 i

private def vertexRankValue_n0_2 (i : ℕ) : ℕ := if i < 160 then vertexRankValue_b4 i else vertexRankValue_b5 i

private def vertexRankValue_n0_3 (i : ℕ) : ℕ := if i < 224 then vertexRankValue_b6 i else vertexRankValue_b7 i

private def vertexRankValue_n0_4 (i : ℕ) : ℕ := if i < 288 then vertexRankValue_b8 i else vertexRankValue_b9 i

private def vertexRankValue_n0_5 (i : ℕ) : ℕ := if i < 352 then vertexRankValue_b10 i else vertexRankValue_b11 i

private def vertexRankValue_n0_6 (i : ℕ) : ℕ := if i < 416 then vertexRankValue_b12 i else vertexRankValue_b13 i

private def vertexRankValue_n0_7 (i : ℕ) : ℕ := if i < 480 then vertexRankValue_b14 i else vertexRankValue_b15 i

private def vertexRankValue_n0_8 (i : ℕ) : ℕ := if i < 544 then vertexRankValue_b16 i else vertexRankValue_b17 i

private def vertexRankValue_n1_0 (i : ℕ) : ℕ := if i < 64 then vertexRankValue_n0_0 i else vertexRankValue_n0_1 i

private def vertexRankValue_n1_1 (i : ℕ) : ℕ := if i < 192 then vertexRankValue_n0_2 i else vertexRankValue_n0_3 i

private def vertexRankValue_n1_2 (i : ℕ) : ℕ := if i < 320 then vertexRankValue_n0_4 i else vertexRankValue_n0_5 i

private def vertexRankValue_n1_3 (i : ℕ) : ℕ := if i < 448 then vertexRankValue_n0_6 i else vertexRankValue_n0_7 i

private def vertexRankValue_n2_0 (i : ℕ) : ℕ := if i < 128 then vertexRankValue_n1_0 i else vertexRankValue_n1_1 i

private def vertexRankValue_n2_1 (i : ℕ) : ℕ := if i < 384 then vertexRankValue_n1_2 i else vertexRankValue_n1_3 i

private def vertexRankValue_n3_0 (i : ℕ) : ℕ := if i < 256 then vertexRankValue_n2_0 i else vertexRankValue_n2_1 i

private def vertexRankValue_n4_0 (i : ℕ) : ℕ := if i < 512 then vertexRankValue_n3_0 i else vertexRankValue_n0_8 i

def vertexRankValue (i : ℕ) : ℕ := vertexRankValue_n4_0 i

end PlanarHom.ColoringMacroFaces.TestFramed
