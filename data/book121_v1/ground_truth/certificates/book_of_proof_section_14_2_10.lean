import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_2_10_certificate :
let A : Set ℝ := {x | ∃ n : ℕ, 1 ≤ n ∧ x = Real.sqrt 2 / (n : ℝ)};
  A.Countable ∧ A.Infinite := by
  dsimp
  constructor
  · exact (Set.countable_range (fun n : ℕ => Real.sqrt 2 / (n : ℝ))).mono (by
      rintro x ⟨n, hn, rfl⟩
      exact ⟨n, rfl⟩)
  · let f : ℕ → ℝ := fun n => Real.sqrt 2 / ((n + 1 : ℕ) : ℝ)
    have hf : Function.Injective f := by
      intro m n h
      have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
      have hm : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hcross :
          Real.sqrt (2 : ℝ) * ((n + 1 : ℕ) : ℝ) =
            Real.sqrt (2 : ℝ) * ((m + 1 : ℕ) : ℝ) :=
        (div_eq_div_iff hm hn).mp h
      have hc : (((n + 1 : ℕ) : ℝ)) = (((m + 1 : ℕ) : ℝ)) :=
        mul_left_cancel₀ hs hcross
      have hnm : n + 1 = m + 1 := by
        exact_mod_cast hc
      exact (Nat.add_right_cancel hnm).symm
    apply (Set.infinite_range_of_injective hf).mono
    rintro x ⟨n, rfl⟩
    exact ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), rfl⟩

#print axioms GroundTruth.book_of_proof_section_14_2_10_certificate
