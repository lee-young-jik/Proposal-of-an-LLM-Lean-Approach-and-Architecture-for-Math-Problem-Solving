import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_9_4_2_certificate :
∃ H : Subgroup (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
  (∀ M : (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
    M ∈ H ↔ ∃ a b : ℝ, (M : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; -b, a]) ∧
  Nonempty (ℂˣ ≃* H) := by
  let ρ : ℂ →+* Matrix (Fin 2) (Fin 2) ℝ :=
    { toFun := fun z => !![z.re, z.im; -z.im, z.re]
      map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
      map_mul' := by
        intro z w
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two, Complex.mul_re, Complex.mul_im] <;> ring
      map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
      map_add' := by intro z w; ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring }
  let f : ℂˣ →* (Matrix (Fin 2) (Fin 2) ℝ)ˣ := Units.map ρ.toMonoidHom
  have hf : Function.Injective f := by
    intro z w h
    have hh := congrArg (fun x : (Matrix (Fin 2) (Fin 2) ℝ)ˣ => (x : Matrix (Fin 2) (Fin 2) ℝ)) h
    apply Units.ext
    apply Complex.ext
    · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hh
    · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hh
  refine ⟨f.range, ?_, ⟨MonoidHom.ofInjective hf⟩⟩
  intro M
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(z : ℂ).re, (z : ℂ).im, rfl⟩
  · rintro ⟨a, b, hm⟩
    let z : ℂ := ⟨a, b⟩
    have hz : z ≠ 0 := by
      intro h
      have ha : a = 0 := congrArg Complex.re h
      have hb : b = 0 := congrArg Complex.im h
      apply Units.ne_zero M
      rw [hm, ha, hb]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    refine ⟨Units.mk0 z hz, ?_⟩
    apply Units.ext
    change ρ z = (M : Matrix (Fin 2) (Fin 2) ℝ)
    exact hm.symm

#print axioms JudsonGold.judson_9_4_2_certificate
