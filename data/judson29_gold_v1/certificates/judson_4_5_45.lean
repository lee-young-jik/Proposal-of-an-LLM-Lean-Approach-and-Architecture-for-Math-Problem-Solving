import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_4_5_45_certificate :
∀ z : ℂˣ, ‖(z : ℂ)‖ ≠ 1 → orderOf z = 0 := by
  intro z hz
  apply orderOf_eq_zero_iff.mpr
  intro h
  apply hz
  apply Complex.norm_eq_one_of_pow_eq_one (n := orderOf z)
  · simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg (fun w : ℂˣ => (w : ℂ)) (pow_orderOf_eq_one z)
  · exact h.orderOf_pos.ne'

#print axioms JudsonGold.judson_4_5_45_certificate
