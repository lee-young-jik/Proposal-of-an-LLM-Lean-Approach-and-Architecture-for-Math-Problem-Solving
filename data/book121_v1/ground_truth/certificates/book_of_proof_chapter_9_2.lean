import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_2_certificate :
∃ (n : ℕ), (1 : ℕ) ≤ n ∧ ¬Nat.Prime ((2 : ℤ) * ↑n ^ (2 : ℕ) - (4 : ℤ) * ↑n + (31 : ℤ)).toNat := by
  refine ⟨31, by norm_num, ?_⟩
  change ¬ Nat.Prime 1829
  intro hp
  have hd : 31 ∣ 1829 := by norm_num
  have h := (Nat.dvd_prime hp).mp hd
  omega

#print axioms GroundTruth.book_of_proof_chapter_9_2_certificate
