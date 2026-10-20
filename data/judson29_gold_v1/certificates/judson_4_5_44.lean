import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_4_5_44_certificate :
∀ (α : Circle) (m n : ℤ),
  (α ^ m = 1 ∧ α ^ n = 1) ↔ α ^ (Int.gcd m n : ℤ) = 1 := by
  intro a m n
  constructor
  · rintro ⟨hm, hn⟩
    rw [Int.gcd_eq_gcd_ab, zpow_add, zpow_mul, zpow_mul, hm, hn]
    simp
  · intro h
    constructor
    · obtain ⟨k, hk⟩ := Int.gcd_dvd_left m n
      rw [hk, zpow_mul, h]
      simp
    · obtain ⟨k, hk⟩ := Int.gcd_dvd_right m n
      rw [hk, zpow_mul, h]
      simp

#print axioms JudsonGold.judson_4_5_44_certificate
