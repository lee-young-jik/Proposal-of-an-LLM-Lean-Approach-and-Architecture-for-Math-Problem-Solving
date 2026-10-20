import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_4_5_26_certificate :
∀ p : ℕ, Nat.Prime p →
  ∀ H : AddSubgroup (ZMod p), H = ⊥ ∨ H = ⊤ := by
  intro p hp H
  haveI : Fact p.Prime := ⟨hp⟩
  exact eq_bot_or_eq_top H

#print axioms JudsonGold.judson_4_5_26_certificate
