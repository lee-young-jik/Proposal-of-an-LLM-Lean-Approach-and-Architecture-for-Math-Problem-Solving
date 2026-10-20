import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_3_5_41_certificate :
∃ H : Subgroup ℝˣ, ∀ x : ℝˣ,
  x ∈ H ↔ ∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
    (x : ℝ) = (a : ℝ) + (b : ℝ) * Real.sqrt 2 := by
  let s : ℝ := Real.sqrt 2
  have hs : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : ∀ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) → (a : ℝ) + (b : ℝ) * s ≠ 0 := by
    intro a b hab he
    by_cases hb : b = 0
    · have ha : a = 0 := by exact_mod_cast (by simpa [hb] using he : (a : ℝ) = 0)
      exact hab.elim (fun h => h ha) (fun h => h hb)
    · have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      have hrat : s = ((-a / b : ℚ) : ℝ) := by
        push_cast
        apply (eq_div_iff hb').mpr
        linarith
      exact irrational_sqrt_two.ne_rat (-a / b) hrat
  let H : Subgroup ℝˣ :=
    { carrier := {x | ∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧ (x : ℝ) = (a : ℝ) + (b : ℝ) * s}
      one_mem' := by refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩; simp
      mul_mem' := by
        rintro x y ⟨a,b,hab,hx⟩ ⟨c,e,hce,hy⟩
        have hv : (x * y : ℝˣ) = x * y := rfl
        have hrep : ((x*y : ℝˣ) : ℝ) = ((a*c+2*b*e : ℚ) : ℝ) + ((a*e+b*c : ℚ) : ℝ)*s := by
          simp only [Units.val_mul, hx, hy]
          push_cast
          ring_nf
          rw [hs]
          ring
        refine ⟨a*c+2*b*e, a*e+b*c, ?_, hrep⟩
        by_contra h
        push_neg at h
        have hz : ((x*y : ℝˣ) : ℝ) = 0 := by rw [hrep,h.1,h.2]; simp
        exact Units.ne_zero (x*y) hz
      inv_mem' := by
        rintro x ⟨a,b,hab,hx⟩
        let δ : ℚ := a^2 - 2*b^2
        have hδ : δ ≠ 0 := by
          intro hz
          have he : ((a : ℝ)+(b : ℝ)*s)*((a : ℝ)-(b : ℝ)*s) = (δ : ℝ) := by
            dsimp [δ]
            push_cast
            ring_nf
            rw [hs]
          have hz' : (δ : ℝ) = 0 := by exact_mod_cast hz
          have hb : a ≠ 0 ∨ -b ≠ 0 := by simpa using hab
          have hnon := mul_ne_zero (hn a b hab) (by simpa [sub_eq_add_neg] using hn a (-b) hb)
          exact hnon (he.trans hz')
        have hδ' : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ
        refine ⟨a/δ, -b/δ, ?_, ?_⟩
        · rcases hab with ha | hb
          · exact Or.inl (div_ne_zero ha hδ)
          · exact Or.inr (div_ne_zero (neg_ne_zero.mpr hb) hδ)
        · rw [Units.val_inv_eq_inv_val]
          rw [hx]
          push_cast
          field_simp [hδ', hn a b hab]
          dsimp [δ]
          push_cast
          ring_nf
          rw [hs] }
  exact ⟨H, fun _ => Iff.rfl⟩

#print axioms JudsonGold.judson_3_5_41_certificate
