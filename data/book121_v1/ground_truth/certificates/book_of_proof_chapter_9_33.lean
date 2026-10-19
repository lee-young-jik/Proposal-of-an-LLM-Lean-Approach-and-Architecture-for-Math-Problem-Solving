import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_33_certificate :
∀ n : ℕ, 1 ≤ n → ∀ a : Fin (n+1) → ℕ, (∀ i, 1 ≤ a i) →
  ∃ k : ℕ, 1 ≤ k ∧ ¬ Nat.Prime (∑ i : Fin (n+1), a i * k^(i.val)) := by
  classical
  intro n hn a ha
  let M : ℕ := ∑ i : Fin (n+1), a i
  have hsize : n+1 ≤ M := by
    calc
      n+1 = ∑ i : Fin (n+1), (1 : ℕ) := by simp
      _ ≤ ∑ i : Fin (n+1), a i := Finset.sum_le_sum (fun i _ => ha i)
  have hM : 2 ≤ M := by omega
  let k : ℕ := M+1
  refine ⟨k, by dsimp [k]; omega, ?_⟩
  intro hp
  have hkm : Nat.ModEq M k 1 := by
    change (M+1) % M = 1 % M
    simp [Nat.add_mod]
  have hterm (i : Fin (n+1)) : Nat.ModEq M (a i*k^i.val) (a i) := by
    simpa using (Nat.ModEq.refl (a i)).mul (hkm.pow i.val)
  have hsum : Nat.ModEq M (∑ i : Fin (n+1), a i*k^i.val) M :=
    Nat.ModEq.sum (fun i _ => hterm i)
  have hzero : Nat.ModEq M M 0 := Nat.modEq_zero_iff_dvd.mpr (dvd_refl M)
  have hdvd : M ∣ ∑ i : Fin (n+1), a i*k^i.val :=
    Nat.modEq_zero_iff_dvd.mp (hsum.trans hzero)
  let j : Fin (n+1) := ⟨1, by omega⟩
  have hj : j.val = 1 := rfl
  have hs : a j*k^j.val ≤ ∑ i : Fin (n+1), a i*k^i.val :=
    Finset.single_le_sum (f := fun i : Fin (n+1) => a i*k^i.val) (fun i _ => Nat.zero_le (a i*k^i.val)) (Finset.mem_univ j)
  have hk : k ≤ a j*k := by
    simpa using Nat.mul_le_mul_right k (ha j)
  rw [hj, pow_one] at hs
  have hsmall : M < ∑ i : Fin (n+1), a i*k^i.val := by
    have hMk : M < k := by dsimp [k]; omega
    omega
  rcases (Nat.dvd_prime hp).mp hdvd with h|h <;> omega

#print axioms GroundTruth.book_of_proof_chapter_9_33_certificate
