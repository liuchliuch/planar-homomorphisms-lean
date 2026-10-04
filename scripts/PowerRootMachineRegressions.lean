import PlanarHom.RationalPowerRootMachines

open PlanarHom Complexity

private theorem size_eq (a k : ℕ) (lo : 2^k ≤ a) (hi : a < 2^(k+1)) :
    Nat.size a = k+1 := by
  have h₁ := Nat.lt_size.mpr lo
  have h₂ := Nat.size_le.mpr hi
  omega

example : NaturalPowerRoot.root 1 0 = 0 := by simpa using NaturalPowerRoot.root_pow 1 (by decide) 0
example : NaturalPowerRoot.root 1 71 = 71 := by simpa using NaturalPowerRoot.root_pow 1 (by decide) 71
example : NaturalPowerRoot.root 2 0 = 0 := by simpa using NaturalPowerRoot.root_pow 2 (by decide) 0
example : NaturalPowerRoot.root 7 1 = 1 := by simpa using NaturalPowerRoot.root_pow 7 (by decide) 1
example : NaturalPowerRoot.root 2 15 = 3 := by
  have hs : Nat.size 15 = 4 := size_eq 15 3 (by norm_num) (by norm_num)
  simp only [NaturalPowerRoot.root, hs]
  norm_num [NaturalPowerRoot.initial, NaturalPowerRoot.step, NaturalPowerRoot.midpoint, Function.iterate_succ_apply]
example : NaturalPowerRoot.root 2 16 = 4 := by
  have hs : Nat.size 16 = 5 := size_eq 16 4 (by norm_num) (by norm_num)
  simp only [NaturalPowerRoot.root, hs]
  norm_num [NaturalPowerRoot.initial, NaturalPowerRoot.step, NaturalPowerRoot.midpoint, Function.iterate_succ_apply]
example : NaturalPowerRoot.root 2 17 = 4 := by
  have hs : Nat.size 17 = 5 := size_eq 17 4 (by norm_num) (by norm_num)
  simp only [NaturalPowerRoot.root, hs]
  norm_num [NaturalPowerRoot.initial, NaturalPowerRoot.step, NaturalPowerRoot.midpoint, Function.iterate_succ_apply]
example : NaturalPowerRoot.root 3 26 = 2 := by
  have hs : Nat.size 26 = 5 := size_eq 26 4 (by norm_num) (by norm_num)
  simp only [NaturalPowerRoot.root, hs]
  norm_num [NaturalPowerRoot.initial, NaturalPowerRoot.step, NaturalPowerRoot.midpoint, Function.iterate_succ_apply]
example : NaturalPowerRoot.root 3 27 = 3 := by
  have hs : Nat.size 27 = 5 := size_eq 27 4 (by norm_num) (by norm_num)
  simp only [NaturalPowerRoot.root, hs]
  norm_num [NaturalPowerRoot.initial, NaturalPowerRoot.step, NaturalPowerRoot.midpoint, Function.iterate_succ_apply]
example : NaturalPowerRoot.root 3 28 = 3 := by
  have hs : Nat.size 28 = 5 := size_eq 28 4 (by norm_num) (by norm_num)
  simp only [NaturalPowerRoot.root, hs]
  norm_num [NaturalPowerRoot.initial, NaturalPowerRoot.step, NaturalPowerRoot.midpoint, Function.iterate_succ_apply]
example : NaturalPowerRoot.root 5 (123 ^ 5) = 123 := NaturalPowerRoot.root_pow 5 (by decide) 123
example : RationalPowerRoot.root 2 0 = 0 := by
  simpa using RationalPowerRoot.root_pow 2 (by decide) 0 (by norm_num)
example : RationalPowerRoot.root 5 ((2/3 : ℚ)^5) = 2/3 :=
  RationalPowerRoot.root_pow 5 (by decide) _ (by norm_num)
example : RationalPowerRoot.root 4 ((137/211 : ℚ)^4) = 137/211 :=
  RationalPowerRoot.root_pow 4 (by decide) _ (by norm_num)

example (n : ℕ) : FP BitEncoding.nat BitEncoding.nat (NaturalPowerRoot.root n) :=
  NaturalPowerRoot.fp_root n
example (n : ℕ) : FP BitEncoding.rat BitEncoding.rat (RationalPowerRoot.root n) :=
  RationalPowerRoot.fp_root n
example (n : ℕ) (hn : n ≠ 0) (x : ℕ) : NaturalPowerRoot.root n (x^n) = x :=
  NaturalPowerRoot.root_pow n hn x
example (n : ℕ) (hn : n ≠ 0) (x : ℚ) (hx : 0 ≤ x) :
    RationalPowerRoot.root n (x^n) = x := RationalPowerRoot.root_pow n hn x hx
