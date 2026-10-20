import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_9_4_22_certificate :
∀ (G : Type) [Group G] [Finite G] (H K : Subgroup G),
  Nat.card G = 20 → Nat.card H = 4 → Nat.card K = 5 →
  (∀ h : H, ∀ k : K, (h : G) * (k : G) = (k : G) * (h : G)) →
  ∀ g : G, ∃! p : H × K, g = (p.1 : G) * (p.2 : G) := by
  intro G _ _ H K hG hH hK hcomm g
  have hc : Subgroup.IsComplement' H K := Subgroup.isComplement'_of_coprime
    (by rw [hH, hK, hG]) (by rw [hH, hK]; decide)
  simpa only [eq_comm] using hc.existsUnique g

#print axioms JudsonGold.judson_9_4_22_certificate
