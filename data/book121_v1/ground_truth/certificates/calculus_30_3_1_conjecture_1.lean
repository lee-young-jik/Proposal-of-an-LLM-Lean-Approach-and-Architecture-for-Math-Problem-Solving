import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_30_3_1_conjecture_1_certificate :
∃ (f : ℝ × ℝ → ℝ),
  (∀ (θ : ℝ),
      ∃ (δ : ℝ), (0 : ℝ) < δ ∧ MonotoneOn (fun (t : ℝ) => f (t * Real.cos θ, t * Real.sin θ)) (Set.Icc (0 : ℝ) δ)) ∧
    ∀ (δ : ℝ), (0 : ℝ) < δ → ∃ (z : ℝ × ℝ), ‖z‖ < δ ∧ f z < f (0 : ℝ × ℝ) := by
  classical
  refine ⟨(fun z : ℝ × ℝ => (z.2 - z.1 ^ 2) * (z.2 - 2 * z.1 ^ 2)), ?_, ?_⟩
  · intro θ
    let a : ℝ := Real.cos θ
    let b : ℝ := Real.sin θ
    have hd (t : ℝ) :
        HasDerivAt
          (fun s : ℝ => (s * b - (s * a) ^ 2) *
            (s * b - 2 * (s * a) ^ 2))
          (2 * t * b ^ 2 - 9 * t ^ 2 * a ^ 2 * b +
            8 * t ^ 3 * a ^ 4) t := by
      convert
        (((hasDerivAt_id t).const_mul b).sub
            (((hasDerivAt_id t).const_mul a).pow 2)).mul
          (((hasDerivAt_id t).const_mul b).sub
            (((((hasDerivAt_id t).const_mul a).pow 2).const_mul 2)))
        using 1 <;> first | (funext s; dsimp; ring) | (dsimp; ring)
    by_cases hb : b = 0
    · refine ⟨1, by norm_num, ?_⟩
      change MonotoneOn
        (fun t : ℝ => (t * b - (t * a) ^ 2) *
          (t * b - 2 * (t * a) ^ 2)) (Set.Icc 0 1)
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (by fun_prop)
        (by fun_prop)
      intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0 < t := ht.1
      rw [(hd t).deriv, hb]
      simp only [mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, sub_zero]
      positivity
    · let d : ℝ := b ^ 2 / (18 * (|a ^ 2 * b| + 1))
      have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
      have hden : 0 < 18 * (|a ^ 2 * b| + 1) := by positivity
      have hdpos : 0 < d := div_pos hb2 hden
      refine ⟨d, hdpos, ?_⟩
      change MonotoneOn
        (fun t : ℝ => (t * b - (t * a) ^ 2) *
          (t * b - 2 * (t * a) ^ 2)) (Set.Icc 0 d)
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 d) (by fun_prop)
        (by fun_prop)
      intro t ht
      rw [(hd t).deriv]
      rw [interior_Icc] at ht
      have ht0 : 0 < t := ht.1
      have htd : t < b ^ 2 / (18 * (|a ^ 2 * b| + 1)) := ht.2
      have hmul : t * (18 * (|a ^ 2 * b| + 1)) < b ^ 2 :=
        (lt_div_iff₀ hden).mp htd
      have hab : a ^ 2 * b ≤ |a ^ 2 * b| := le_abs_self _
      have hcomp : t * (a ^ 2 * b) ≤ t * |a ^ 2 * b| :=
        mul_le_mul_of_nonneg_left hab ht0.le
      have hlast : 0 ≤ 8 * t ^ 3 * a ^ 4 := by positivity
      nlinarith
  · intro δ hδ
    let x : ℝ := min δ 1 / 4
    have hminpos : 0 < min δ 1 := lt_min hδ (by norm_num)
    have hxpos : 0 < x := by
      dsimp [x]
      positivity
    have hxδ : x < δ := by
      dsimp [x]
      have hle : min δ 1 ≤ δ := min_le_left _ _
      nlinarith
    have hxone : x ≤ 1 / 4 := by
      dsimp [x]
      exact div_le_div_of_nonneg_right (min_le_right δ 1) (by norm_num)
    have hypos : 0 ≤ (3 / 2 : ℝ) * x ^ 2 := by positivity
    have hyx : (3 / 2 : ℝ) * x ^ 2 < x := by
      nlinarith [sq_nonneg x]
    refine ⟨(x, (3 / 2 : ℝ) * x ^ 2), ?_, ?_⟩
    · rw [Prod.norm_def]
      simp only [Real.norm_eq_abs, max_lt_iff]
      rw [abs_of_pos hxpos, abs_of_nonneg hypos]
      exact ⟨hxδ, lt_trans hyx hxδ⟩
    · change (((3 / 2 : ℝ) * x ^ 2 - x ^ 2) *
        ((3 / 2 : ℝ) * x ^ 2 - 2 * x ^ 2)) <
        ((0 : ℝ) - 0 ^ 2) * ((0 : ℝ) - 2 * 0 ^ 2)
      have hx4 : 0 < x ^ 4 := pow_pos hxpos 4
      nlinarith

#print axioms GroundTruth.calculus_30_3_1_conjecture_1_certificate
