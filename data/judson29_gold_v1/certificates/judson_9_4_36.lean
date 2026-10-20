import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_9_4_36_certificate :
∀ B : (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
  ∃ f : Matrix.SpecialLinearGroup (Fin 2) ℝ ≃* Matrix.SpecialLinearGroup (Fin 2) ℝ,
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ((f A) : Matrix (Fin 2) (Fin 2) ℝ) =
        (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) *
        (A : Matrix (Fin 2) (Fin 2) ℝ) * (B : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro B
  let C : Matrix (Fin 2) (Fin 2) ℝ := B
  let D : Matrix (Fin 2) (Fin 2) ℝ := ↑(B⁻¹)
  have hCD : C * D = 1 := B.val_inv
  have hDC : D * C = 1 := B.inv_val
  let f : Matrix.SpecialLinearGroup (Fin 2) ℝ → Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    fun A => ⟨D * (A : Matrix (Fin 2) (Fin 2) ℝ) * C, by
      change Matrix.det ((↑(B⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) * (A : Matrix (Fin 2) (Fin 2) ℝ) * (↑B : Matrix (Fin 2) (Fin 2) ℝ)) = 1
      rw [Matrix.det_units_conj']
      exact A.property⟩
  let g : Matrix.SpecialLinearGroup (Fin 2) ℝ → Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    fun A => ⟨C * (A : Matrix (Fin 2) (Fin 2) ℝ) * D, by
      change Matrix.det ((↑B : Matrix (Fin 2) (Fin 2) ℝ) * (A : Matrix (Fin 2) (Fin 2) ℝ) * (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) ℝ)) = 1
      rw [Matrix.det_units_conj]
      exact A.property⟩
  refine ⟨{ toFun := f, invFun := g, left_inv := ?_, right_inv := ?_, map_mul' := ?_ }, fun _ => rfl⟩
  · intro A
    apply Subtype.ext
    change C * (D * (A : Matrix (Fin 2) (Fin 2) ℝ) * C) * D = _
    calc
      _ = (C * D) * (A : Matrix (Fin 2) (Fin 2) ℝ) * (C * D) := by noncomm_ring
      _ = (A : Matrix (Fin 2) (Fin 2) ℝ) := by rw [hCD]; simp
  · intro A
    apply Subtype.ext
    change D * (C * (A : Matrix (Fin 2) (Fin 2) ℝ) * D) * C = _
    calc
      _ = (D * C) * (A : Matrix (Fin 2) (Fin 2) ℝ) * (D * C) := by noncomm_ring
      _ = (A : Matrix (Fin 2) (Fin 2) ℝ) := by rw [hDC]; simp
  · intro A E
    apply Subtype.ext
    change D * ((A : Matrix (Fin 2) (Fin 2) ℝ) * (E : Matrix (Fin 2) (Fin 2) ℝ)) * C = (D * (A : Matrix (Fin 2) (Fin 2) ℝ) * C) * (D * (E : Matrix (Fin 2) (Fin 2) ℝ) * C)
    calc
      _ = D * (A : Matrix (Fin 2) (Fin 2) ℝ) * (C * D) * (E : Matrix (Fin 2) (Fin 2) ℝ) * C := by rw [hCD]; simp [mul_assoc]
      _ = _ := by noncomm_ring

#print axioms JudsonGold.judson_9_4_36_certificate
