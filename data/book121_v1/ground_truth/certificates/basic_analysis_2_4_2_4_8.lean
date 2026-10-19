import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.basic_analysis_2_4_2_4_8_certificate :
∃ (u : ℕ → ℝ),
  CauchySeq u ∧ ∀ (M : ℕ), (1 : ℕ) ≤ M → ∃ (n : ℕ), M ≤ n ∧ |u n - u (n - (1 : ℕ))| < |u (n + (1 : ℕ)) - u n| := by
  classical
  let u : ℕ → ℝ := fun n => if n % 3 = 0 then (1/2 : ℝ)^n else 0
  have hg : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hu : Tendsto u atTop (nhds 0) := by
    apply squeeze_zero (g := fun n : ℕ => (1/2 : ℝ)^n) ?_ ?_ hg
    · intro n; dsimp [u]; split_ifs <;> first | exact le_rfl | positivity
    · intro n; dsimp [u]; split_ifs <;> first | exact le_rfl | positivity
  have hc : CauchySeq u := hu.cauchySeq
  refine ⟨u, hc, ?_⟩
  intro M hM
  let n : ℕ := 3*(M+1)+2
  have hn : M ≤ n := by dsimp [n]; omega
  have hn0 : n % 3 ≠ 0 := by dsimp [n]; omega
  have hn1 : (n-1) % 3 ≠ 0 := by dsimp [n]; omega
  have hn2 : (n+1) % 3 = 0 := by dsimp [n]; omega
  refine ⟨n, hn, ?_⟩
  have hp : 0 < (1/2 : ℝ)^(n+1) := by positivity
  simpa only [u, if_neg hn0, if_neg hn1, if_pos hn2, sub_self, sub_zero, abs_zero] using (abs_pos.mpr (ne_of_gt hp))

#print axioms GroundTruth.basic_analysis_2_4_2_4_8_certificate
