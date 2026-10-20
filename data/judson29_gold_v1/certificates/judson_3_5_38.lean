import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_3_5_38_certificate :
(∀ n : ℕ, ∃ H : AddSubgroup ℤ,
    ∀ z : ℤ, z ∈ H ↔ ∃ k : ℤ, z = (n : ℤ) * k) ∧
  (∀ H : AddSubgroup ℤ, ∃ n : ℕ,
    ∀ z : ℤ, z ∈ H ↔ ∃ k : ℤ, z = (n : ℤ) * k) := by
  constructor
  · intro n
    refine ⟨AddSubgroup.zmultiples (n : ℤ), ?_⟩
    intro z
    simp [Int.mem_zmultiples_iff, dvd_def]
  · intro H
    obtain ⟨n, hn⟩ := (AddSubgroup.le_zmultiples_iff (1 : ℤ) H).mp (by simp)
    refine ⟨n, ?_⟩
    intro z
    simp only [nsmul_eq_mul, mul_one] at hn
    rw [hn]
    simp [Int.mem_zmultiples_iff, dvd_def]

#print axioms JudsonGold.judson_3_5_38_certificate
