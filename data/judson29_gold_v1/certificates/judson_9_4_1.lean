import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_9_4_1_certificate :
∀ n : ℤ, n ≠ 0 →
  Nonempty (ℤ ≃+ AddSubgroup.zmultiples n) := by
  intro n hn
  let f : ℤ →+ ℤ := zmultiplesHom ℤ n
  have hi : Function.Injective f := by
    intro a b h
    change a * n = b * n at h
    exact mul_right_cancel₀ hn h
  exact ⟨AddMonoidHom.ofInjective hi⟩

#print axioms JudsonGold.judson_9_4_1_certificate
