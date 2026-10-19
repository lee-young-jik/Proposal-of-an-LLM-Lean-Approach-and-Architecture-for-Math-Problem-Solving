import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_5D_19_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ (T : V →ₗ[F] V) (U : Submodule F V),
  ∀ h : ∀ u ∈ U, T u ∈ U,
  (∃ n : ℕ, ∃ b : Module.Basis (Fin n) F U, ∀ i j : Fin n, i ≠ j → LinearMap.toMatrix b b (T.restrict h) i j = 0) →
  (∃ n : ℕ, ∃ b : Module.Basis (Fin n) F (V ⧸ U), ∀ i j : Fin n, i ≠ j → LinearMap.toMatrix b b (U.mapQ U T h) i j = 0) → (∃ n : ℕ, ∃ b : Module.Basis (Fin n) F V, ∀ i j : Fin n, i ≠ j → LinearMap.toMatrix b b T i j = 0)
) := by
  intro H
  let T : ℂ →ₗ[ℝ] ℂ := Complex.imLm.smulRight (1 : ℂ)
  let U : Submodule ℝ ℂ := LinearMap.ker Complex.imLm
  have hTU : ∀ z : ℂ, T z ∈ U := by
    intro z
    change Complex.imLm (T z) = 0
    simp [T]
  have h : ∀ u ∈ U, T u ∈ U := by
    intro u hu
    exact hTU u
  have hres : T.restrict h = 0 := by
    ext u
    change T (u : ℂ) = 0
    have hu : Complex.imLm (u : ℂ) = 0 := u.property
    simp [T, hu]
  have hquot : U.mapQ U T h = 0 := by
    ext z
    change Submodule.Quotient.mk (T z) = 0
    exact (Submodule.Quotient.mk_eq_zero U).mpr (hTU z)
  have hdres : ∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℝ U,
      ∀ i j : Fin n, i ≠ j →
        LinearMap.toMatrix b b (T.restrict h) i j = 0 := by
    let b := Module.finBasis ℝ U
    refine ⟨Module.finrank ℝ U, b, ?_⟩
    intro i j hij
    simp [hres]
  have hdquot : ∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℝ (ℂ ⧸ U),
      ∀ i j : Fin n, i ≠ j →
        LinearMap.toMatrix b b (U.mapQ U T h) i j = 0 := by
    let b := Module.finBasis ℝ (ℂ ⧸ U)
    refine ⟨Module.finrank ℝ (ℂ ⧸ U), b, ?_⟩
    intro i j hij
    simp [hquot]
  obtain ⟨n, b, hd⟩ := H ℝ ℂ T U h hdres hdquot
  let M : Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix b b T
  have heigen : ∀ j : Fin n, T (b j) = M j j • b j := by
    intro j
    apply b.repr.injective
    ext i
    have he : (b.repr (T (b j))) i = M i j := by dsimp [M]; rw [LinearMap.toMatrix_apply]
    rw [he]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst i
      simp
    · have hh : M i j = 0 := hd i j hij
      rw [hh]
      simp [hij,Ne.symm hij]
  have hnil : ∀ z : ℂ, T (T z) = 0 := by
    intro z
    simp [T]
  have hdiagzero : ∀ j : Fin n, M j j = 0 := by
    intro j
    have hs : (M j j * M j j) • b j = 0 := by
      calc
        (M j j * M j j) • b j = M j j • (M j j • b j) := by
          rw [mul_smul]
        _ = M j j • T (b j) := by rw [heigen j]
        _ = T (M j j • b j) := by rw [map_smul]
        _ = T (T (b j)) := by rw [heigen j]
        _ = 0 := hnil (b j)
    have hmul : M j j * M j j = 0 := by
      exact (smul_eq_zero.mp hs).resolve_right (b.ne_zero j)
    exact (mul_self_eq_zero.mp hmul)
  have hzero : T = 0 := by
    apply b.ext
    intro j
    rw [LinearMap.zero_apply, heigen j, hdiagzero j, zero_smul]
  have hi := LinearMap.congr_fun hzero Complex.I
  simp [T] at hi

#print axioms GroundTruth.linear_algebra_5D_19_certificate
