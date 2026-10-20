import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_3_5_26_certificate :
∀ n : ℕ, 2 < n → ∃ k : (ZMod n)ˣ, k ^ 2 = 1 ∧ k ≠ 1 := by
  intro n hn
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨-1, by simp, ?_⟩
  intro h
  have hh : (-1 : ZMod n) = 1 := congrArg (fun x : (ZMod n)ˣ => (x : ZMod n)) h
  have hh2 : (2 : ZMod n) = 0 := by linear_combination -hh
  have hd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp hh2
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

#print axioms JudsonGold.judson_3_5_26_certificate
