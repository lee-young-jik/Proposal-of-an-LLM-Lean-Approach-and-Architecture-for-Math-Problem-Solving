import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_3_5_32_certificate :
∀ (G : Type) [Group G] [Finite G], Even (Nat.card G) →
  ∃ a : G, a ≠ 1 ∧ a ^ 2 = 1 := by
  intro G _ _ he
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (even_iff_two_dvd.mp he)
  refine ⟨a, ?_, ?_⟩
  · intro h
    simp [h] at ha
  · simpa [ha] using pow_orderOf_eq_one a

#print axioms JudsonGold.judson_3_5_32_certificate
