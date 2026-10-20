import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_4_5_32_certificate :
∀ (G : Type) [Group G] [Finite G] (x : G),
  Subgroup.zpowers x = ⊤ → ∀ k : ℕ, Nat.Coprime k (Nat.card G) →
  Subgroup.zpowers (x ^ k) = ⊤ := by
  intro G _ _ x hx k hk
  have ho : orderOf x = Nat.card G := by
    exact orderOf_eq_card_of_forall_mem_zpowers (fun g => by rw [hx]; trivial)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := x) (by simpa [ho] using hk)
  apply le_antisymm le_top
  rw [← hx]
  apply Subgroup.zpowers_le.mpr
  have hmem : (x ^ k) ^ m ∈ Subgroup.zpowers (x ^ k) := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m
  simpa only [hm] using hmem

#print axioms JudsonGold.judson_4_5_32_certificate
