import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_23_certificate :
∀ x y : ℝ, x^3 < y^3 → x < y := by
  intro x y h
  exact (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).lt_iff_lt.mp h

#print axioms GroundTruth.book_of_proof_chapter_9_23_certificate
