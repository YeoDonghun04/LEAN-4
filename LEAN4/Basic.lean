/-
Copyright (c) 2025 Kdmsi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kdmsi
-/
module
public import Mathlib

/-! Examples of multiplication identities. -/

/-ex2.1.1-/
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b,mul_assoc,mul_comm c a]
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc,mul_comm a b,mul_assoc]

/-ex2.1.2-/
example (a b c d e f : ℝ) (h : b * c = e * f) :
    a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c, mul_assoc a e f]
  rw [h]

example (a b c d : ℝ) (hyp : c = b * a - d)
    (hyp' : d = a * b) : c = 0 := by
  rw[hyp,hyp',mul_comm b a,sub_self]

/-ex2.1.3-/
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  calc
    (a + b) * (a - b) = a * a + b * a - (a * b + b * b) := by
      rw[mul_sub,add_mul,add_mul]
    _ = a * a - b * b := by
      rw[←sub_sub, ←add_sub,mul_comm b a, sub_self, add_zero]
    _ = a ^ 2 - b ^ 2 := by
      rw[←pow_two,←pow_two]
