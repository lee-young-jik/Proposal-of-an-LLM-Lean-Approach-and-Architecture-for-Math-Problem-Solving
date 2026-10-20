import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_4_5_39_certificate :
∀ (G : Type) [Group G] [Finite G] [IsCyclic G] (d : ℕ),
  d ∣ Nat.card G → ∃ H : Subgroup G, Nat.card H = d := by
  intro G _ _ _ d hd
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  refine ⟨Subgroup.zpowers (x ^ (orderOf x / d)), ?_⟩
  rw [Nat.card_zpowers]
  apply orderOf_pow_orderOf_div
  · rw [hx]
    exact Nat.card_pos.ne'
  · simpa [hx] using hd

#print axioms JudsonGold.judson_4_5_39_certificate
