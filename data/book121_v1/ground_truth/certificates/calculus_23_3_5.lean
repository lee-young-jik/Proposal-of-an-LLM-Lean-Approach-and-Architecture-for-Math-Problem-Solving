import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_23_3_5_certificate :
∀ L : ℝ, ¬ Tendsto (fun z : ℝ × ℝ => (3*z.1^2*z.2^2) / (7*z.1^6+4*z.2^3))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (7*z.1^6+4*z.2^3) ≠ 0}) (nhds L) := by
  classical
  intro L h
  let S : Set (ℝ × ℝ) :=
    {z | z ≠ 0 ∧ (7 * z.1 ^ 6 + 4 * z.2 ^ 3) ≠ 0}
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hp₀ : Tendsto (fun t : ℝ => (t, 0)) (𝓝[≠] 0)
      (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (nhds 0) := tendsto_const_nhds
      simpa only [← nhds_prod_eq] using ht.prodMk hzero
    · filter_upwards [self_mem_nhdsWithin] with t ht'
      have ht0 : t ≠ 0 := by simpa using ht'
      simp [S, ht0]
  have hp₁ : Tendsto (fun t : ℝ => (t, t ^ 2)) (𝓝[≠] 0)
      (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa only [← nhds_prod_eq, zero_pow (by norm_num : (2:ℕ) ≠ 0)] using ht.prodMk (ht.pow 2)
    · filter_upwards [self_mem_nhdsWithin] with t ht'
      have ht0 : t ≠ 0 := by simpa using ht'
      constructor
      · intro hz
        have hz' := congrArg Prod.fst hz
        exact ht0 (by simpa using hz')
      · rw [show 7 * t ^ 6 + 4 * (t ^ 2) ^ 3 = 11 * t ^ 6 by ring]
        exact mul_ne_zero (by norm_num) (pow_ne_zero 6 ht0)
  have h₀ := h.comp hp₀
  have h₁ := h.comp hp₁
  have h₀' : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₀.congr'
    filter_upwards with t
    simp [Function.comp_apply]
  have h₁' : Tendsto (fun _ : ℝ => (3 / 11 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₁.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht'
    have ht0 : t ≠ 0 := by simpa using ht'
    simp only [Function.comp_apply]
    rw [show 3 * t ^ 2 * (t ^ 2) ^ 2 = 3 * t ^ 6 by ring]
    rw [show 7 * t ^ 6 + 4 * (t ^ 2) ^ 3 = 11 * t ^ 6 by ring]
    field_simp [ht0]
  have hL0 : L = 0 := tendsto_nhds_unique h₀' tendsto_const_nhds
  have hL1 : L = 3 / 11 := tendsto_nhds_unique h₁' tendsto_const_nhds
  rw [hL0] at hL1
  norm_num at hL1

#print axioms GroundTruth.calculus_23_3_5_certificate
