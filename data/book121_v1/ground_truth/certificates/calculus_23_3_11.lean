import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_23_3_11_certificate :
∀ L : ℝ, ¬ Tendsto (fun z : ℝ × ℝ => (z.1^4+z.2^8) / (z.1^2*z.2^2))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (z.1^2*z.2^2) ≠ 0}) (nhds L) := by
  classical
  intro L h
  let S : Set (ℝ × ℝ) := {z | z ≠ 0 ∧ (z.1 ^ 2 * z.2 ^ 2) ≠ 0}
  have hp₁ : Tendsto (fun t : ℝ => (t, t)) (𝓝[≠] 0)
      (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Tendsto (fun t : ℝ => (t, t)) (𝓝 0)
          (𝓝 (0 : ℝ × ℝ)) := by
        simpa using (by fun_prop : Continuous (fun t : ℝ => (t, t))).tendsto (0 : ℝ)
      exact hcont.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have hp₂ : Tendsto (fun t : ℝ => (t ^ 2, t)) (𝓝[≠] 0)
      (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Tendsto (fun t : ℝ => (t ^ 2, t)) (𝓝 0)
          (𝓝 (0 : ℝ × ℝ)) := by
        simpa using (by fun_prop : Continuous (fun t : ℝ => (t ^ 2, t))).tendsto (0 : ℝ)
      exact hcont.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have hpath₁ := h.comp hp₁
  have hpath₂ := h.comp hp₂
  have hcalc₁ : Tendsto (fun t : ℝ => 1 + t ^ 4) (𝓝[≠] 0) (𝓝 L) := by
    apply hpath₁.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp only [Function.comp_apply]
    field_simp [ht0] <;> ring
  have hcalc₂ : Tendsto (fun t : ℝ => 2 * t ^ 2) (𝓝[≠] 0) (𝓝 L) := by
    apply hpath₂.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp only [Function.comp_apply]
    field_simp [ht0] <;> ring
  have hlim₁ : Tendsto (fun t : ℝ => 1 + t ^ 4) (𝓝[≠] 0) (𝓝 (1 : ℝ)) := by
    have hcont : Tendsto (fun t : ℝ => 1 + t ^ 4) (𝓝 0) (𝓝 (1 : ℝ)) := by
      simpa using (by fun_prop : Continuous (fun t : ℝ => 1 + t ^ 4)).tendsto (0 : ℝ)
    exact hcont.mono_left inf_le_left
  have hlim₂ : Tendsto (fun t : ℝ => 2 * t ^ 2) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    have hcont : Tendsto (fun t : ℝ => 2 * t ^ 2) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa using (by fun_prop : Continuous (fun t : ℝ => 2 * t ^ 2)).tendsto (0 : ℝ)
    exact hcont.mono_left inf_le_left
  have hL1 : L = 1 := tendsto_nhds_unique hcalc₁ hlim₁
  have hL0 : L = 0 := tendsto_nhds_unique hcalc₂ hlim₂
  linarith

#print axioms GroundTruth.calculus_23_3_11_certificate
