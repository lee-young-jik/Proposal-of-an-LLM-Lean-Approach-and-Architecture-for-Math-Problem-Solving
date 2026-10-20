import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_9_4_8_certificate :
¬ Nonempty (ℚ ≃+ ℤ) := by
  rintro ⟨e⟩
  let q : ℚ := e.symm 1 / 2
  have hh : (2 : ℤ) * e q = 1 := by
    calc
      2 * e q = e q + e q := by ring
      _ = e (q + q) := (e.map_add q q).symm
      _ = e (e.symm 1) := by congr 1; dsimp [q]; ring
      _ = 1 := e.apply_symm_apply 1
  omega

#print axioms JudsonGold.judson_9_4_8_certificate
