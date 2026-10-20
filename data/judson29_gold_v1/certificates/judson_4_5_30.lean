import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_4_5_30_certificate :
∀ (G : Type) [Group G] (a b : G) (m n : ℕ),
  orderOf a = m → orderOf b = n → 0 < m → 0 < n →
  Nat.Coprime m n → Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  intro G _ a b m n ha hb hm hn hc
  apply le_antisymm
  · intro x hx
    have hxa : orderOf x ∣ m := by
      rw [← ha]
      exact orderOf_dvd_of_mem_zpowers hx.1
    have hxb : orderOf x ∣ n := by
      rw [← hb]
      exact orderOf_dvd_of_mem_zpowers hx.2
    have hx1 : orderOf x ∣ 1 := by simpa [hc.gcd_eq_one] using Nat.dvd_gcd hxa hxb
    simpa using orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hx1)
  · exact bot_le

#print axioms JudsonGold.judson_4_5_30_certificate
