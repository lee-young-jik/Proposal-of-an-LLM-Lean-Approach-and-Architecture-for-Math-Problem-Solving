import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_23_3_9_certificate :
∀ L : ℝ, ¬ Tendsto (fun z : ℝ × ℝ => (z.1^2) / (z.1^2+z.2^2))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (z.1^2+z.2^2) ≠ 0}) (nhds L) := by
  classical
  intro L h
  let S : Set (ℝ × ℝ) := {z | z ≠ 0 ∧ (z.1^2 + z.2^2) ≠ 0}
  have hp₁ : Tendsto (fun t : ℝ => (t, 0)) (𝓝[≠] 0) (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).prodMk continuousAt_const).tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have hp₀ : Tendsto (fun t : ℝ => (0, t)) (𝓝[≠] 0) (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact ((continuousAt_const.prodMk (continuousAt_id : ContinuousAt (fun t : ℝ => t) 0)).tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have h₁ := h.comp hp₁
  have h₀ := h.comp hp₀
  have h₁' : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₁.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp only [Function.comp_apply, Prod.fst, Prod.snd, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
    exact div_self (pow_ne_zero 2 ht0)
  have h₀' : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₀.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp [Function.comp_apply, ht0]
  have hL1 : L = 1 := tendsto_nhds_unique h₁' tendsto_const_nhds
  have hL0 : L = 0 := tendsto_nhds_unique h₀' tendsto_const_nhds
  rw [hL0] at hL1
  norm_num at hL1

#print axioms GroundTruth.calculus_23_3_9_certificate
