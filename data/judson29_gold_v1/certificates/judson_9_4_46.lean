import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_9_4_46_certificate :
∀ (G H : Type) [Group G] [Group H], Nonempty (G ≃* H) →
  ∀ n : ℕ, 0 < n → (∃ K : Subgroup G, Nat.card K = n) →
    ∃ L : Subgroup H, Nat.card L = n := by
  intro G H _ _ he n hn hk
  obtain ⟨e⟩ := he
  obtain ⟨K, hK⟩ := hk
  refine ⟨K.map e.toMonoidHom, ?_⟩
  rw [← hK]
  exact Nat.card_congr (e.subgroupMap K).toEquiv.symm

#print axioms JudsonGold.judson_9_4_46_certificate
