import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.basic_analysis_2_2_2_2_7_certificate :
∃ u : ℕ → ℝ,
  (∃ l : ℝ, Tendsto (fun n : ℕ => u (n^2)) atTop (nhds l)) ∧
  ∀ L : ℝ, ¬ Tendsto u atTop (nhds L) := by
  classical
  let u : ℕ → ℝ := fun n => if ∃ k : ℕ, n = k^2 then 0 else 1
  have h0 : ∀ n : ℕ, u (n^2) = 0 := by intro n; simp [u]
  have h1 : ∀ n : ℕ, 1 ≤ n → u (n^2+1) = 1 := by
    intro n hn
    have hns : ¬ ∃ k : ℕ, n^2+1 = k^2 := by
      rintro ⟨k, hk⟩
      by_cases hkn : k ≤ n
      · nlinarith [Nat.pow_le_pow_left hkn 2]
      · have hnk : n+1 ≤ k := by omega
        nlinarith [Nat.pow_le_pow_left hnk 2]
    simp [u, hns]
  have ht0 : Tendsto (fun n : ℕ => n^2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max b 1)] with n hn
    have hb : b ≤ n := (le_max_left b 1).trans hn
    have hn1 : 1 ≤ n := (le_max_right b 1).trans hn
    nlinarith
  have ht1 : Tendsto (fun n : ℕ => n^2+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max b 1)] with n hn
    have hb : b ≤ n := (le_max_left b 1).trans hn
    have hn1 : 1 ≤ n := (le_max_right b 1).trans hn
    nlinarith
  refine ⟨u, ⟨0, ?_⟩, ?_⟩
  · simpa only [h0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · intro L hL
    have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds L) := by
      simpa only [Function.comp_def, h0] using hL.comp ht0
    have ho : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds L) := by
      apply (hL.comp ht1).congr'
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact h1 n hn
    have hL0 : L = 0 := tendsto_nhds_unique hz tendsto_const_nhds
    have hL1 : L = 1 := tendsto_nhds_unique ho tendsto_const_nhds
    linarith

#print axioms GroundTruth.basic_analysis_2_2_2_2_7_certificate
