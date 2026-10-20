import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_4_5_14_certificate :
let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0];
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, -1];
  IsOfFinOrder A ∧ IsOfFinOrder B ∧ ¬ IsOfFinOrder (A * B) := by
  dsimp only
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, -1]
  change IsOfFinOrder A ∧ IsOfFinOrder B ∧ ¬ IsOfFinOrder (A * B)
  refine ⟨?_, ?_, ?_⟩
  · apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨4, by decide, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, pow_succ, Matrix.mul_fin_two]
  · apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨3, by decide, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [B, pow_succ, Matrix.mul_fin_two]
  · intro h
    have hp : ∀ n : ℕ, (A * B) ^ n = !![1, -(n : ℝ); 0, 1] := by
      intro n
      induction n with
      | zero => ext i j; fin_cases i <;> fin_cases j <;> norm_num
      | succ n ih =>
        rw [pow_succ, ih]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [A, B, Matrix.mul_fin_two, Nat.cast_add] <;> ring
    obtain ⟨n, hn, he⟩ := h.exists_pow_eq_one
    have hx := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) he
    rw [hp] at hx
    simp at hx
    exact (Nat.ne_of_gt hn) (by exact_mod_cast hx)

#print axioms JudsonGold.judson_4_5_14_certificate
