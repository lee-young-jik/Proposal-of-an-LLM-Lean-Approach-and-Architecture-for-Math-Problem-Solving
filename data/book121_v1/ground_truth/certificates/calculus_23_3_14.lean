import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_23_3_14_certificate :
∃ (f : ℝ × ℝ → ℝ),
  (∀ (v : ℝ × ℝ), v ≠ (0 : ℝ × ℝ) → Tendsto (fun (t : ℝ) => f (t * v.1, t * v.2)) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ))) ∧
    ¬Tendsto f (𝓝[≠] (0 : ℝ × ℝ)) (𝓝 (0 : ℝ)) := by
  classical
  refine ⟨fun z : ℝ × ℝ => z.1 * z.2 ^ 3 / (z.1 ^ 2 + z.2 ^ 6), ?_, ?_⟩
  · intro v hv
    rcases v with ⟨a, b⟩
    by_cases ha : a = 0
    · simp [ha]
    · let g : ℝ → ℝ := fun t => t ^ 2 * a * b ^ 3 / (a ^ 2 + t ^ 4 * b ^ 6)
      have hden : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
      have hg : Tendsto g (𝓝[≠] 0) (𝓝 0) := by
        have hc : ContinuousAt g 0 := by
          apply ContinuousAt.div
          · fun_prop
          · fun_prop
          · simpa [g] using hden
        simpa [g] using hc.tendsto.mono_left inf_le_left
      apply hg.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
      dsimp [g]
      have haux : a ^ 2 + t ^ 4 * b ^ 6 ≠ 0 := by
        have hpos : 0 < a ^ 2 := sq_pos_of_ne_zero ha
        positivity
      field_simp [ht, ha, haux]
      all_goals ring
  · intro h
    have hp0 : Tendsto (fun t : ℝ => (t ^ 3, t)) (𝓝[≠] 0) (𝓝 (0 : ℝ × ℝ)) := by
      have hc : Tendsto (fun t : ℝ => (t^3,t)) (nhds (0 : ℝ)) (nhds (0 : ℝ × ℝ)) := by
        simpa using ((continuous_id.pow 3).prodMk continuous_id).tendsto (0 : ℝ)
      simpa using hc.mono_left inf_le_left
    have hp : Tendsto (fun t : ℝ => (t ^ 3, t)) (𝓝[≠] 0) (𝓝[≠] (0 : ℝ × ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hp0, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
      intro hz
      apply ht
      exact congrArg Prod.snd hz
    have hc : Tendsto
        (fun t : ℝ => (t ^ 3) * t ^ 3 / ((t ^ 3) ^ 2 + t ^ 6))
        (𝓝[≠] 0) (𝓝 0) := by
      simpa only [Function.comp_apply] using h.comp hp
    have heq :
        (fun t : ℝ => (t ^ 3) * t ^ 3 / ((t ^ 3) ^ 2 + t ^ 6)) =ᶠ[𝓝[≠] 0]
          fun _ : ℝ => (1 / 2 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
      field_simp [ht]
      all_goals ring
    have hc' : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) (𝓝[≠] 0) (𝓝 0) :=
      hc.congr' heq
    have hconst : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    have hz : (0 : ℝ) = 1 / 2 := tendsto_nhds_unique hc' hconst
    norm_num at hz

#print axioms GroundTruth.calculus_23_3_14_certificate
