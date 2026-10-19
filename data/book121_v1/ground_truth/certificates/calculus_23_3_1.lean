import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_23_3_1_certificate :
∃ L : ℝ, Tendsto (fun z : ℝ × ℝ => (z.1*z.2) / (Real.sqrt (z.1^2+z.2^2)))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (Real.sqrt (z.1^2+z.2^2)) ≠ 0}) (nhds L) := by
  refine ⟨0, ?_⟩
  let F := nhdsWithin (0 : ℝ × ℝ)
    {z : ℝ × ℝ | z ≠ 0 ∧ Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≠ 0}
  have hx : Tendsto (fun z : ℝ × ℝ => z.1) F (nhds 0) :=
    (continuous_fst.tendsto (0 : ℝ × ℝ)).mono_left inf_le_left
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : ∀ᶠ z in F, dist z.1 0 < ε :=
    (Metric.tendsto_nhds.1 hx) ε hε
  filter_upwards [he, self_mem_nhdsWithin] with z hz hzd
  have hr0 : 0 < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hzd.2)
  have hy2 : z.2 ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
    nlinarith [sq_nonneg z.1]
  have hy : |z.2| ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hy2
  have hb : |z.1 * z.2 / Real.sqrt (z.1 ^ 2 + z.2 ^ 2)| ≤ |z.1| := by
    rw [abs_div, abs_mul, abs_of_pos hr0]
    apply (div_le_iff₀ hr0).2
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hy (abs_nonneg z.1)
  have hz' : |z.1| < ε := by
    simpa [Real.dist_eq] using hz
  rw [Real.dist_eq, sub_zero]
  exact lt_of_le_of_lt hb hz'

#print axioms GroundTruth.calculus_23_3_1_certificate
