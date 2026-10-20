import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_4_5_34_certificate :
∀ (G : Type) [CommGroup G] [Finite G] (p q : ℕ),
  Nat.card G = p * q → Nat.Coprime p q →
  (∃ a : G, orderOf a = p) → (∃ b : G, orderOf b = q) → IsCyclic G := by
  intro G _ _ p q hcard hc ha hb
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  apply isCyclic_of_orderOf_eq_card (a * b)
  rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (Commute.all a b)]
  · simpa [ha, hb] using hcard.symm
  · simpa [ha, hb] using hc

#print axioms JudsonGold.judson_4_5_34_certificate
