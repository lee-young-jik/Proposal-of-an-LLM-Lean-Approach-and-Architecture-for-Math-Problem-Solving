import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_23_3_2_certificate :
∃ L : ℝ, Tendsto (fun z : ℝ × ℝ => (z.1^2*z.2^2) / (z.1^2+z.2^2))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (z.1^2+z.2^2) ≠ 0}) (nhds L) := by
  refine ⟨0, ?_⟩
  let F := nhdsWithin (0 : ℝ × ℝ)
    {z : ℝ × ℝ | z ≠ 0 ∧ z.1 ^ 2 + z.2 ^ 2 ≠ 0}
  have hx : Tendsto (fun z : ℝ × ℝ => z.1) F (nhds 0) :=
    (continuous_fst.tendsto (0 : ℝ × ℝ)).mono_left inf_le_left
  have hx2 : Tendsto (fun z : ℝ × ℝ => z.1 ^ 2) F (nhds 0) := by
    simpa using hx.pow 2
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : ∀ᶠ z in F, dist (z.1 ^ 2) 0 < ε :=
    (Metric.tendsto_nhds.1 hx2) ε hε
  filter_upwards [he, self_mem_nhdsWithin] with z hz hzd
  have hd : 0 < z.1 ^ 2 + z.2 ^ 2 := by
    have hn : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
    exact lt_of_le_of_ne hn (Ne.symm hzd.2)
  have hv : 0 ≤ z.1 ^ 2 * z.2 ^ 2 / (z.1 ^ 2 + z.2 ^ 2) := by
    positivity
  have hb : z.1 ^ 2 * z.2 ^ 2 / (z.1 ^ 2 + z.2 ^ 2) ≤ z.1 ^ 2 := by
    apply (div_le_iff₀ hd).2
    have hy : z.2 ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
      nlinarith [sq_nonneg z.1]
    nlinarith [mul_le_mul_of_nonneg_left hy (sq_nonneg z.1)]
  have hz' : z.1 ^ 2 < ε := by
    simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg z.1)] using hz
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hv]
  exact lt_of_le_of_lt hb hz'

#print axioms GroundTruth.calculus_23_3_2_certificate
