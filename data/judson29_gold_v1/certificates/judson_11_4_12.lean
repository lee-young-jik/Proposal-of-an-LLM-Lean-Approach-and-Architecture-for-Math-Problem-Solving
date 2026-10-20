import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_11_4_12_certificate :
∀ (G : Type) [Group G] (H : Subgroup G) (k : ℕ),
  0 < k → Nat.card H = k →
  (∀ K : Subgroup G, Nat.card K = k → K = H) → H.Normal := by
  intro G _ H k hk hcard huniq
  constructor
  intro x hx g
  let e := MulAut.conj g
  have hm : H.map e.toMonoidHom = H := by
    apply huniq
    rw [← hcard]
    exact Nat.card_congr (e.subgroupMap H).toEquiv.symm
  rw [← hm]
  exact ⟨x, hx, rfl⟩

#print axioms JudsonGold.judson_11_4_12_certificate
