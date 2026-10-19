import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_23_3_4_certificate :
∀ L : ℝ, ¬ Tendsto (fun z : ℝ × ℝ => (z.1^2*z.2) / (z.1^3+z.2^3))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (z.1^3+z.2^3) ≠ 0}) (nhds L) := by
  classical
  intro L h
  let S : Set (ℝ × ℝ) := {z | z ≠ 0 ∧ (z.1^3 + z.2^3) ≠ 0}
  have hp₀ : Tendsto (fun t : ℝ => (t, 0)) (𝓝[≠] 0) (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).prodMk continuousAt_const).tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have hp₁ : Tendsto (fun t : ℝ => (t, t)) (𝓝[≠] 0) (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).prodMk continuousAt_id).tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      constructor
      · simp [ht0]
      · rw [show t^3 + t^3 = 2*t^3 by ring]
        exact mul_ne_zero (by norm_num) (pow_ne_zero 3 ht0)
  have h₀ := h.comp hp₀
  have h₁ := h.comp hp₁
  have h₀' : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₀.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp [Function.comp_apply, ht0]
  have h₁' : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₁.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp only [Function.comp_apply, Prod.fst, Prod.snd]
    field_simp [ht0]
    ring
  have hL0 : L = 0 := tendsto_nhds_unique h₀' tendsto_const_nhds
  have hL1 : L = 1 / 2 := tendsto_nhds_unique h₁' tendsto_const_nhds
  rw [hL0] at hL1
  norm_num at hL1

#print axioms GroundTruth.calculus_23_3_4_certificate
