import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.basic_analysis_6_1_6_1_10_b_certificate :
∀ (f : ℕ → ℝ → ℝ) (x : ℕ → ℝ),
  (∀ (n : ℕ), (1 : ℕ) ≤ n → x n ∈ Set.Icc (0 : ℝ) (1 : ℝ) ∧ f n (x n) = (1 : ℝ)) →
    (∀ (m n : ℕ), (1 : ℕ) ≤ m → (1 : ℕ) ≤ n → x m = x n → m = n) →
      ∃ (ε : ℝ), (0 : ℝ) < ε ∧ ∀ (N : ℕ), ∃ (n : ℕ), N ≤ n ∧ ∃ y ∈ Set.Icc (0 : ℝ) (1 : ℝ), ε ≤ |f n y| := by
  intro f x hf hx
  refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
  intro N
  let n : ℕ := max N 1
  have hnN : N ≤ n := le_max_left N 1
  have hn1 : 1 ≤ n := le_max_right N 1
  refine ⟨n, hnN, x n, (hf n hn1).1, ?_⟩
  rw [(hf n hn1).2]
  norm_num

#print axioms GroundTruth.basic_analysis_6_1_6_1_10_b_certificate
