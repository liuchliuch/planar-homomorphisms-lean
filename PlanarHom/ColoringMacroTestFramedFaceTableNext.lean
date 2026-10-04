import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.TestFramed
private def nextValue_b0 (i : ℕ) : ℕ :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 38 else 8) else (if i < 3 then 80 else 10)) else (if i < 6 then (if i < 5 then 64 else 12) else (if i < 7 then 556 else 14))) else (if i < 12 then (if i < 10 then (if i < 9 then 11 else 7) else (if i < 11 then 13 else 1)) else (if i < 14 then (if i < 13 then 15 else 3) else (if i < 15 then 9 else 5)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 52 else 24) else (if i < 19 then 134 else 26)) else (if i < 22 then (if i < 21 then 103 else 28) else (if i < 23 then 97 else 30))) else (if i < 28 then (if i < 26 then (if i < 25 then 27 else 23) else (if i < 27 then 29 else 17)) else (if i < 30 then (if i < 29 then 31 else 19) else (if i < 31 then 25 else 21)))))

private def nextValue_b1 (i : ℕ) : ℕ :=
  (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 464 else 40) else (if i < 35 then 18 else 42)) else (if i < 38 then (if i < 37 then 2 else 44) else (if i < 39 then 523 else 46))) else (if i < 44 then (if i < 42 then (if i < 41 then 43 else 39) else (if i < 43 then 45 else 33)) else (if i < 46 then (if i < 45 then 47 else 35) else (if i < 47 then 41 else 37)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 81 else 56) else (if i < 51 then 36 else 58)) else (if i < 54 then (if i < 53 then 98 else 60) else (if i < 55 then 84 else 62))) else (if i < 60 then (if i < 58 then (if i < 57 then 59 else 55) else (if i < 59 then 61 else 49)) else (if i < 62 then (if i < 61 then 63 else 51) else (if i < 63 then 57 else 53)))))

private def nextValue_b2 (i : ℕ) : ℕ :=
  (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 83 else 72) else (if i < 67 then 95 else 74)) else (if i < 70 then (if i < 69 then 96 else 76) else (if i < 71 then 487 else 78))) else (if i < 76 then (if i < 74 then (if i < 73 then 75 else 71) else (if i < 75 then 77 else 65)) else (if i < 78 then (if i < 77 then 79 else 67) else (if i < 79 then 73 else 69)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 50 else 82) else (if i < 83 then 89 else 4)) else (if i < 86 then (if i < 85 then 86 else 48) else (if i < 87 then 54 else 88))) else (if i < 92 then (if i < 90 then (if i < 89 then 92 else 85) else (if i < 91 then 94 else 87)) else (if i < 94 then (if i < 93 then 91 else 66) else (if i < 95 then 68 else 93)))))

private def nextValue_b3 (i : ℕ) : ℕ :=
  (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 99 else 70) else (if i < 99 then 16 else 90)) else (if i < 102 then (if i < 101 then 110 else 136) else (if i < 103 then 112 else 133))) else (if i < 108 then (if i < 106 then (if i < 105 then 114 else 485) else (if i < 107 then 108 else 139)) else (if i < 110 then (if i < 109 then 115 else 100) else (if i < 111 then 109 else 102)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 111 else 104) else (if i < 115 then 113 else 106)) else (if i < 118 then (if i < 117 then 126 else 34) else (if i < 119 then 128 else 144))) else (if i < 124 then (if i < 122 then (if i < 121 then 130 else 147) else (if i < 123 then 124 else 148)) else (if i < 126 then (if i < 125 then 131 else 116) else (if i < 127 then 125 else 118)))))

private def nextValue_b4 (i : ℕ) : ℕ :=
  (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 127 else 120) else (if i < 131 then 129 else 122)) else (if i < 134 then (if i < 133 then 101 else 20) else (if i < 135 then 117 else 132))) else (if i < 140 then (if i < 138 then (if i < 137 then 140 else 107) else (if i < 139 then 142 else 137)) else (if i < 142 then (if i < 141 then 135 else 138) else (if i < 143 then 145 else 150)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 146 else 141) else (if i < 147 then 119 else 143)) else (if i < 150 then (if i < 149 then 504 else 121) else (if i < 151 then 149 else 105))) else (if i < 156 then (if i < 154 then (if i < 153 then 190 else 160) else (if i < 155 then 232 else 162)) else (if i < 158 then (if i < 157 then 216 else 164) else (if i < 159 then 550 else 166)))))

private def nextValue_b5 (i : ℕ) : ℕ :=
  (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 163 else 159) else (if i < 163 then 165 else 153)) else (if i < 166 then (if i < 165 then 167 else 155) else (if i < 167 then 161 else 157))) else (if i < 172 then (if i < 170 then (if i < 169 then 204 else 176) else (if i < 171 then 286 else 178)) else (if i < 174 then (if i < 173 then 255 else 180) else (if i < 175 then 249 else 182)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 179 else 175) else (if i < 179 then 181 else 169)) else (if i < 182 then (if i < 181 then 183 else 171) else (if i < 183 then 177 else 173))) else (if i < 188 then (if i < 186 then (if i < 185 then 478 else 192) else (if i < 187 then 170 else 194)) else (if i < 190 then (if i < 189 then 154 else 196) else (if i < 191 then 511 else 198)))))

private def nextValue_b6 (i : ℕ) : ℕ :=
  (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 195 else 191) else (if i < 195 then 197 else 185)) else (if i < 198 then (if i < 197 then 199 else 187) else (if i < 199 then 193 else 189))) else (if i < 204 then (if i < 202 then (if i < 201 then 233 else 208) else (if i < 203 then 188 else 210)) else (if i < 206 then (if i < 205 then 250 else 212) else (if i < 207 then 236 else 214)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 211 else 207) else (if i < 211 then 213 else 201)) else (if i < 214 then (if i < 213 then 215 else 203) else (if i < 215 then 209 else 205))) else (if i < 220 then (if i < 218 then (if i < 217 then 235 else 224) else (if i < 219 then 247 else 226)) else (if i < 222 then (if i < 221 then 248 else 228) else (if i < 223 then 459 else 230)))))

private def nextValue_b7 (i : ℕ) : ℕ :=
  (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 227 else 223) else (if i < 227 then 229 else 217)) else (if i < 230 then (if i < 229 then 231 else 219) else (if i < 231 then 225 else 221))) else (if i < 236 then (if i < 234 then (if i < 233 then 202 else 234) else (if i < 235 then 241 else 156)) else (if i < 238 then (if i < 237 then 238 else 200) else (if i < 239 then 206 else 240)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 244 else 237) else (if i < 243 then 246 else 239)) else (if i < 246 then (if i < 245 then 243 else 218) else (if i < 247 then 220 else 245))) else (if i < 252 then (if i < 250 then (if i < 249 then 251 else 222) else (if i < 251 then 168 else 242)) else (if i < 254 then (if i < 253 then 262 else 288) else (if i < 255 then 264 else 285)))))

private def nextValue_b8 (i : ℕ) : ℕ :=
  (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 266 else 457) else (if i < 259 then 260 else 291)) else (if i < 262 then (if i < 261 then 267 else 252) else (if i < 263 then 261 else 254))) else (if i < 268 then (if i < 266 then (if i < 265 then 263 else 256) else (if i < 267 then 265 else 258)) else (if i < 270 then (if i < 269 then 278 else 186) else (if i < 271 then 280 else 296)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 282 else 299) else (if i < 275 then 276 else 300)) else (if i < 278 then (if i < 277 then 283 else 268) else (if i < 279 then 277 else 270))) else (if i < 284 then (if i < 282 then (if i < 281 then 279 else 272) else (if i < 283 then 281 else 274)) else (if i < 286 then (if i < 285 then 253 else 172) else (if i < 287 then 269 else 284)))))

private def nextValue_b9 (i : ℕ) : ℕ :=
  (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 292 else 259) else (if i < 291 then 294 else 289)) else (if i < 294 then (if i < 293 then 287 else 290) else (if i < 295 then 297 else 302))) else (if i < 300 then (if i < 298 then (if i < 297 then 298 else 293) else (if i < 299 then 271 else 295)) else (if i < 302 then (if i < 301 then 500 else 273) else (if i < 303 then 301 else 257)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 342 else 312) else (if i < 307 then 384 else 314)) else (if i < 310 then (if i < 309 then 368 else 316) else (if i < 311 then 562 else 318))) else (if i < 316 then (if i < 314 then (if i < 313 then 315 else 311) else (if i < 315 then 317 else 305)) else (if i < 318 then (if i < 317 then 319 else 307) else (if i < 319 then 313 else 309)))))

private def nextValue_b10 (i : ℕ) : ℕ :=
  (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 356 else 328) else (if i < 323 then 438 else 330)) else (if i < 326 then (if i < 325 then 407 else 332) else (if i < 327 then 401 else 334))) else (if i < 332 then (if i < 330 then (if i < 329 then 331 else 327) else (if i < 331 then 333 else 321)) else (if i < 334 then (if i < 333 then 335 else 323) else (if i < 335 then 329 else 325)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 492 else 344) else (if i < 339 then 322 else 346)) else (if i < 342 then (if i < 341 then 306 else 348) else (if i < 343 then 535 else 350))) else (if i < 348 then (if i < 346 then (if i < 345 then 347 else 343) else (if i < 347 then 349 else 337)) else (if i < 350 then (if i < 349 then 351 else 339) else (if i < 351 then 345 else 341)))))

private def nextValue_b11 (i : ℕ) : ℕ :=
  (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 385 else 360) else (if i < 355 then 340 else 362)) else (if i < 358 then (if i < 357 then 402 else 364) else (if i < 359 then 388 else 366))) else (if i < 364 then (if i < 362 then (if i < 361 then 363 else 359) else (if i < 363 then 365 else 353)) else (if i < 366 then (if i < 365 then 367 else 355) else (if i < 367 then 361 else 357)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 387 else 376) else (if i < 371 then 399 else 378)) else (if i < 374 then (if i < 373 then 400 else 380) else (if i < 375 then 473 else 382))) else (if i < 380 then (if i < 378 then (if i < 377 then 379 else 375) else (if i < 379 then 381 else 369)) else (if i < 382 then (if i < 381 then 383 else 371) else (if i < 383 then 377 else 373)))))

private def nextValue_b12 (i : ℕ) : ℕ :=
  (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 354 else 386) else (if i < 387 then 393 else 308)) else (if i < 390 then (if i < 389 then 390 else 352) else (if i < 391 then 358 else 392))) else (if i < 396 then (if i < 394 then (if i < 393 then 396 else 389) else (if i < 395 then 398 else 391)) else (if i < 398 then (if i < 397 then 395 else 370) else (if i < 399 then 372 else 397)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 403 else 374) else (if i < 403 then 320 else 394)) else (if i < 406 then (if i < 405 then 414 else 440) else (if i < 407 then 416 else 437))) else (if i < 412 then (if i < 410 then (if i < 409 then 418 else 507) else (if i < 411 then 412 else 443)) else (if i < 414 then (if i < 413 then 419 else 404) else (if i < 415 then 413 else 406)))))

private def nextValue_b13 (i : ℕ) : ℕ :=
  (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 415 else 408) else (if i < 419 then 417 else 410)) else (if i < 422 then (if i < 421 then 430 else 338) else (if i < 423 then 432 else 448))) else (if i < 428 then (if i < 426 then (if i < 425 then 434 else 451) else (if i < 427 then 428 else 452)) else (if i < 430 then (if i < 429 then 435 else 420) else (if i < 431 then 429 else 422)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 431 else 424) else (if i < 435 then 433 else 426)) else (if i < 438 then (if i < 437 then 405 else 324) else (if i < 439 then 421 else 436))) else (if i < 444 then (if i < 442 then (if i < 441 then 444 else 411) else (if i < 443 then 446 else 441)) else (if i < 446 then (if i < 445 then 439 else 442) else (if i < 447 then 449 else 454)))))

private def nextValue_b14 (i : ℕ) : ℕ :=
  (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 450 else 445) else (if i < 451 then 423 else 447)) else (if i < 454 then (if i < 453 then 502 else 425) else (if i < 455 then 453 else 409))) else (if i < 460 then (if i < 458 then (if i < 457 then 466 else 505) else (if i < 459 then 468 else 174)) else (if i < 462 then (if i < 461 then 462 else 526) else (if i < 463 then 469 else 32)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 463 else 456) else (if i < 467 then 465 else 458)) else (if i < 470 then (if i < 469 then 467 else 460) else (if i < 471 then 480 else 275))) else (if i < 476 then (if i < 474 then (if i < 473 then 482 else 326) else (if i < 475 then 476 else 514)) else (if i < 478 then (if i < 477 then 483 else 184) else (if i < 479 then 477 else 470)))))

private def nextValue_b15 (i : ℕ) : ℕ :=
  (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 479 else 472) else (if i < 483 then 481 else 474)) else (if i < 486 then (if i < 485 then 494 else 427) else (if i < 487 then 496 else 22))) else (if i < 492 then (if i < 490 then (if i < 489 then 490 else 538) else (if i < 491 then 497 else 336)) else (if i < 494 then (if i < 493 then 491 else 484) else (if i < 495 then 493 else 486)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 495 else 488) else (if i < 499 then 303 else 503)) else (if i < 502 then (if i < 501 then 506 else 499) else (if i < 503 then 151 else 501))) else (if i < 508 then (if i < 506 then (if i < 505 then 123 else 498) else (if i < 507 then 471 else 455)) else (if i < 510 then (if i < 509 then 516 else 310) else (if i < 511 then 512 else 548)))))

private def nextValue_b16 (i : ℕ) : ℕ :=
  (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 519 else 475) else (if i < 515 then 513 else 508)) else (if i < 518 then (if i < 517 then 515 else 546) else (if i < 519 then 517 else 510))) else (if i < 524 then (if i < 522 then (if i < 521 then 528 else 158) else (if i < 523 then 524 else 554)) else (if i < 526 then (if i < 525 then 531 else 461) else (if i < 527 then 525 else 520)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 527 else 552) else (if i < 531 then 529 else 522)) else (if i < 534 then (if i < 533 then 540 else 6) else (if i < 535 then 536 else 560))) else (if i < 540 then (if i < 538 then (if i < 537 then 543 else 489) else (if i < 539 then 537 else 532)) else (if i < 542 then (if i < 541 then 539 else 558) else (if i < 543 then 541 else 534)))))

private def nextValue_b17 (i : ℕ) : ℕ :=
  (if i < 557 then (if i < 550 then (if i < 547 then (if i < 545 then 509 else (if i < 546 then 569 else 518)) else (if i < 548 then 545 else (if i < 549 then 152 else 547))) else (if i < 553 then (if i < 551 then 521 else (if i < 552 then 549 else 530)) else (if i < 555 then (if i < 554 then 551 else 0) else (if i < 556 then 553 else 533)))) else (if i < 563 then (if i < 560 then (if i < 558 then 555 else (if i < 559 then 542 else 557)) else (if i < 561 then 304 else (if i < 562 then 559 else 564))) else (if i < 566 then (if i < 564 then 561 else (if i < 565 then 566 else 563)) else (if i < 568 then (if i < 567 then 568 else 565) else (if i < 569 then 544 else 567)))))

private def nextValue_n0_0 (i : ℕ) : ℕ := if i < 32 then nextValue_b0 i else nextValue_b1 i

private def nextValue_n0_1 (i : ℕ) : ℕ := if i < 96 then nextValue_b2 i else nextValue_b3 i

private def nextValue_n0_2 (i : ℕ) : ℕ := if i < 160 then nextValue_b4 i else nextValue_b5 i

private def nextValue_n0_3 (i : ℕ) : ℕ := if i < 224 then nextValue_b6 i else nextValue_b7 i

private def nextValue_n0_4 (i : ℕ) : ℕ := if i < 288 then nextValue_b8 i else nextValue_b9 i

private def nextValue_n0_5 (i : ℕ) : ℕ := if i < 352 then nextValue_b10 i else nextValue_b11 i

private def nextValue_n0_6 (i : ℕ) : ℕ := if i < 416 then nextValue_b12 i else nextValue_b13 i

private def nextValue_n0_7 (i : ℕ) : ℕ := if i < 480 then nextValue_b14 i else nextValue_b15 i

private def nextValue_n0_8 (i : ℕ) : ℕ := if i < 544 then nextValue_b16 i else nextValue_b17 i

private def nextValue_n1_0 (i : ℕ) : ℕ := if i < 64 then nextValue_n0_0 i else nextValue_n0_1 i

private def nextValue_n1_1 (i : ℕ) : ℕ := if i < 192 then nextValue_n0_2 i else nextValue_n0_3 i

private def nextValue_n1_2 (i : ℕ) : ℕ := if i < 320 then nextValue_n0_4 i else nextValue_n0_5 i

private def nextValue_n1_3 (i : ℕ) : ℕ := if i < 448 then nextValue_n0_6 i else nextValue_n0_7 i

private def nextValue_n2_0 (i : ℕ) : ℕ := if i < 128 then nextValue_n1_0 i else nextValue_n1_1 i

private def nextValue_n2_1 (i : ℕ) : ℕ := if i < 384 then nextValue_n1_2 i else nextValue_n1_3 i

private def nextValue_n3_0 (i : ℕ) : ℕ := if i < 256 then nextValue_n2_0 i else nextValue_n2_1 i

private def nextValue_n4_0 (i : ℕ) : ℕ := if i < 512 then nextValue_n3_0 i else nextValue_n0_8 i

def nextValue (i : ℕ) : ℕ := nextValue_n4_0 i

end PlanarHom.ColoringMacroFaces.TestFramed
