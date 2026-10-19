import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.basic_analysis_6_1_6_1_10_a_certificate :
∃ f : ℕ → ℝ → ℝ, ∃ x : ℕ → ℝ,
  (∀ n, 1 ≤ n → x n ∈ Set.Icc (0 : ℝ) 1 ∧ f n (x n) = 1) ∧
  (∀ m n, 1 ≤ m → 1 ≤ n → x m = x n → m = n) ∧
  (∀ y ∈ Set.Icc (0 : ℝ) 1, Tendsto (fun n => f n y) atTop (nhds 0)) := by
  classical
  let x : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let f : ℕ → ℝ → ℝ := fun n y => if y = x n then 1 else 0
  have hxinj : Function.Injective x := by
    intro m n hmn
    dsimp [x] at hmn
    have hm : (m : ℝ) + 1 ≠ 0 := by
      have hm0 : 0 < (m : ℝ) + 1 := by
        exact_mod_cast Nat.zero_lt_succ m
      exact ne_of_gt hm0
    have hn : (n : ℝ) + 1 ≠ 0 := by
      have hn0 : 0 < (n : ℝ) + 1 := by
        exact_mod_cast Nat.zero_lt_succ n
      exact ne_of_gt hn0
    rw [div_eq_div_iff hm hn] at hmn
    have hcast : (m : ℝ) = (n : ℝ) := by linarith
    exact_mod_cast hcast
  refine ⟨f, x, ?_, ?_, ?_⟩
  · intro n hn
    constructor
    · constructor
      · dsimp [x]
        have hd : 0 ≤ (n : ℝ) + 1 := by
          have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        exact div_nonneg (by norm_num) hd
      · dsimp [x]
        have hd : 0 < (n : ℝ) + 1 := by
          exact_mod_cast Nat.zero_lt_succ n
        apply (div_le_one hd).2
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
    · simp [f]
  · intro m n hm hn h
    exact hxinj h
  · intro y hy
    by_cases h : ∃ k, y = x k
    · obtain ⟨k, hk⟩ := h
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (k + 1)] with n hn
      have hne : y ≠ x n := by
        intro heq
        have hxn : x k = x n := hk.symm.trans heq
        have hkn : k = n := hxinj hxn
        omega
      simp [f, hne]
    · apply tendsto_const_nhds.congr'
      filter_upwards [] with n
      have hne : y ≠ x n := by
        intro heq
        exact h ⟨n, heq⟩
      simp [f, hne]

#print axioms GroundTruth.basic_analysis_6_1_6_1_10_a_certificate
