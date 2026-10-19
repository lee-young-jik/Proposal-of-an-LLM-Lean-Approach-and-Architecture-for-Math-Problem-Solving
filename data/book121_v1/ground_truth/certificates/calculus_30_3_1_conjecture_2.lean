import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_30_3_1_conjecture_2_certificate :
¬ (
∀ f : (ℝ × ℝ) → ℝ, (DifferentiableAt ℝ f (0 : ℝ × ℝ) ∧ fderiv ℝ f (0 : ℝ × ℝ) = 0 ∧
  (∀ δ : ℝ, 0 < δ → ∃ x y : ℝ × ℝ, ‖x‖ < δ ∧ ‖y‖ < δ ∧ f x < f 0 ∧ f 0 < f y)) →
  ∃ θ φ : Fin 2 → ℝ,
  (0 ≤ θ 0 ∧ θ 0 < 2*Real.pi) ∧
  (∀ i, θ i < φ i) ∧
  (∀ i j, i < j → φ i < θ j) ∧
  φ (Fin.last 1) < θ 0 + 2*Real.pi ∧
  (∀ i, ∃ δ : ℝ, 0 < δ ∧ MonotoneOn (fun t : ℝ => f (t * Real.cos (θ i), t * Real.sin (θ i))) (Set.Icc 0 δ)) ∧
  (∀ i, ∃ δ : ℝ, 0 < δ ∧ AntitoneOn (fun t : ℝ => f (t * Real.cos (φ i), t * Real.sin (φ i))) (Set.Icc 0 δ))
) := by
  rintro h
  let f : (ℝ × ℝ) → ℝ := fun p => (p.2 - p.1 ^ 2) * (p.2 - 2 * p.1 ^ 2)
  have hfd : HasFDerivAt f (0 : (ℝ × ℝ) →L[ℝ] ℝ) (0 : ℝ × ℝ) := by
    dsimp [f]
    convert
      (((hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).sub
          ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).pow 2)).mul
        ((hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).sub
          ((hasFDerivAt_const (𝕜 := ℝ) (x := (0 : ℝ × ℝ)) (c := (2 : ℝ))).mul
            ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).pow 2)))) using 1 <;>
      simp
  have hsaddle :
      DifferentiableAt ℝ f (0 : ℝ × ℝ) ∧
        fderiv ℝ f (0 : ℝ × ℝ) = 0 ∧
        ∀ δ : ℝ, 0 < δ →
          ∃ x y : ℝ × ℝ,
            ‖x‖ < δ ∧ ‖y‖ < δ ∧ f x < f 0 ∧ f 0 < f y := by
    refine ⟨hfd.differentiableAt, hfd.fderiv, ?_⟩
    intro δ hδ
    let q : ℝ := min δ 1 / 4
    have hmin : 0 < min δ 1 := lt_min hδ zero_lt_one
    have hq : 0 < q := by dsimp [q]; positivity
    have hqδ : q < δ := by
      dsimp [q]
      have hm : min δ 1 ≤ δ := min_le_left _ _
      nlinarith
    have hq1 : q ≤ 1 / 4 := by
      dsimp [q]
      have hm : min δ 1 ≤ 1 := min_le_right _ _
      nlinarith
    refine ⟨(q, (3 / 2 : ℝ) * q ^ 2), (q, 0), ?_, ?_, ?_, ?_⟩
    · rw [Prod.norm_def]
      simp only [Real.norm_eq_abs, abs_of_pos hq]
      have hsecond : (3 / 2 : ℝ) * q ^ 2 < q := by nlinarith [sq_nonneg q]
      have habs : |(3 / 2 : ℝ) * q ^ 2| < δ := by
        rw [abs_of_nonneg]
        · exact lt_trans hsecond hqδ
        · positivity
      exact max_lt hqδ habs
    · rw [Prod.norm_def]
      simpa [Real.norm_eq_abs, abs_of_pos hq, hqδ] using hδ
    · dsimp [f]
      nlinarith [pow_pos hq 4]
    · dsimp [f]
      nlinarith [pow_pos hq 4]
  obtain ⟨θ, φ, hθ, hθφ, hsep, hlast, hmono, hanti⟩ := h f hsaddle
  obtain ⟨δ, hδ, ha⟩ := hanti (0 : Fin 2)
  let a : ℝ := Real.cos (φ (0 : Fin 2))
  let b : ℝ := Real.sin (φ (0 : Fin 2))
  have hab : a ^ 2 + b ^ 2 = 1 := by
    dsimp [a, b]
    nlinarith [Real.sin_sq_add_cos_sq (φ (0 : Fin 2))]
  by_cases hbpos : 0 < b
  · let t : ℝ := min (δ / 2) (b / (4 * (a ^ 2 + 1)))
    have hden : 0 < 4 * (a ^ 2 + 1) := by positivity
    have ht : 0 < t := by
      dsimp [t]
      apply lt_min
      · linarith
      · positivity
    have htδ : t ≤ δ := by
      dsimp [t]
      have hm : min (δ / 2) (b / (4 * (a ^ 2 + 1))) ≤ δ / 2 := min_le_left _ _
      linarith
    have htbound : t * a ^ 2 < b / 4 := by
      have hm : t ≤ b / (4 * (a ^ 2 + 1)) := by
        dsimp [t]
        exact min_le_right _ _
      have ha2 : a ^ 2 < a ^ 2 + 1 := by linarith
      calc
        t * a ^ 2 < t * (a ^ 2 + 1) := mul_lt_mul_of_pos_left ha2 ht
        _ ≤ (b / (4 * (a ^ 2 + 1))) * (a ^ 2 + 1) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
        _ = b / 4 := by field_simp <;> ring
    have htmem : t ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt ht, htδ⟩
    have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) δ := ⟨le_rfl, le_of_lt hδ⟩
    have hle := ha hzero htmem (le_of_lt ht)
    have hpositive : 0 < f (t * a, t * b) := by
      have hpa : 0 < b-t*a^2 := by linarith
      have hpb : 0 < b-2*t*a^2 := by linarith
      have he : f (t*a,t*b) = (t*(b-t*a^2))*(t*(b-2*t*a^2)) := by dsimp [f]; ring
      rw [he]
      exact mul_pos (mul_pos ht hpa) (mul_pos ht hpb)
    have hrewrite :
        f (t * Real.cos (φ (0 : Fin 2)), t * Real.sin (φ (0 : Fin 2))) =
          f (t * a, t * b) := by rfl
    dsimp only at hle
    rw [hrewrite] at hle
    have hfzero : f (0 * Real.cos (φ (0 : Fin 2)), 0 * Real.sin (φ (0 : Fin 2))) = 0 := by
      simp [f]
    rw [hfzero] at hle
    linarith
  · have hb : b ≤ 0 := le_of_not_gt hbpos
    let t : ℝ := δ / 2
    have ht : 0 < t := by dsimp [t]; linarith
    have htδ : t ≤ δ := by dsimp [t]; linarith
    have htmem : t ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt ht, htδ⟩
    have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) δ := ⟨le_rfl, le_of_lt hδ⟩
    have hle := ha hzero htmem (le_of_lt ht)
    have hpositive : 0 < f (t * a, t * b) := by
      have htb : t*b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le hb
      by_cases ha0 : a = 0
      · have hbneg : b < 0 := by rw [ha0] at hab; nlinarith
        have htbneg : t*b < 0 := mul_neg_of_pos_of_neg ht hbneg
        dsimp [f]
        rw [ha0]
        simp only [mul_zero, zero_pow, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, sub_zero]
        exact mul_pos_of_neg_of_neg htbneg htbneg
      · have hta : 0 < (t*a)^2 := sq_pos_of_ne_zero (mul_ne_zero ht.ne' ha0)
        have h1 : t*b-(t*a)^2 < 0 := by linarith
        have h2 : t*b-2*(t*a)^2 < 0 := by linarith
        exact mul_pos_of_neg_of_neg h1 h2
    have hrewrite :
        f (t * Real.cos (φ (0 : Fin 2)), t * Real.sin (φ (0 : Fin 2))) =
          f (t * a, t * b) := by rfl
    dsimp only at hle
    rw [hrewrite] at hle
    have hfzero : f (0 * Real.cos (φ (0 : Fin 2)), 0 * Real.sin (φ (0 : Fin 2))) = 0 := by
      simp [f]
    rw [hfzero] at hle
    linarith

#print axioms GroundTruth.calculus_30_3_1_conjecture_2_certificate
