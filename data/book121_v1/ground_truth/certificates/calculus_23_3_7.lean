import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_23_3_7_certificate :
¬Continuous fun (z : ℝ × ℝ) =>
    if z = (0 : ℝ × ℝ) then (1 : ℝ) else Real.sin (z.1 * z.2) / (z.1 ^ (2 : ℕ) + z.2 ^ (2 : ℕ)) := by
  classical
  intro h
  let f : ℝ × ℝ → ℝ := fun z => if z = 0 then 1 else Real.sin (z.1*z.2) / (z.1^2 + z.2^2)
  have hp : Tendsto (fun t : ℝ => (t, 0)) (𝓝[≠] 0) (𝓝 (0 : ℝ × ℝ)) := by
    exact (((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).prodMk continuousAt_const).tendsto).mono_left inf_le_left
  have hf : Tendsto (fun t : ℝ => f (t, 0)) (𝓝[≠] 0) (𝓝 (f 0)) := by
    exact h.continuousAt.tendsto.comp hp
  have hf1 : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (𝓝 (1 : ℝ)) := by
    have heq : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (𝓝 (f 0)) := by
      apply hf.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [f, ht0]
    simpa [f] using heq
  have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := tendsto_const_nhds
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique hf1 hzero
  norm_num at h10

#print axioms GroundTruth.calculus_23_3_7_certificate
