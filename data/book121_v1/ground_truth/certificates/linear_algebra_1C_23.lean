import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_1C_23_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V],
  ∀ V₁ V₂ U : Submodule F V, IsCompl V₁ U → IsCompl V₂ U → V₁ = V₂
) := by
  classical
  intro h
  let U : Submodule ℝ (ℝ × ℝ) := LinearMap.ker (LinearMap.snd ℝ ℝ ℝ)
  let V₁ : Submodule ℝ (ℝ × ℝ) := LinearMap.ker (LinearMap.fst ℝ ℝ ℝ)
  let V₂ : Submodule ℝ (ℝ × ℝ) := LinearMap.ker (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ)
  have h₁ : IsCompl V₁ U := by
    constructor
    · apply Submodule.disjoint_def.mpr
      intro x hx hy
      have hx' : x.1 = 0 := hx
      have hy' : x.2 = 0 := hy
      exact Prod.ext hx' hy'
    · rw [codisjoint_iff]
      apply top_unique
      intro x hx
      exact Submodule.mem_sup.mpr ⟨(0,x.2), by simp [V₁, LinearMap.mem_ker], (x.1,0), by simp [U, LinearMap.mem_ker], by ext <;> simp⟩
  have h₂ : IsCompl V₂ U := by
    constructor
    · apply Submodule.disjoint_def.mpr
      intro x hx hy
      have hx' : x.1 - x.2 = 0 := hx
      have hy' : x.2 = 0 := hy
      apply Prod.ext
      · dsimp; linarith
      · exact hy'
    · rw [codisjoint_iff]
      apply top_unique
      intro x hx
      exact Submodule.mem_sup.mpr ⟨(x.2,x.2), by simp [V₂, LinearMap.mem_ker], (x.1-x.2,0), by simp [U, LinearMap.mem_ker], by ext <;> simp⟩
  have heq := h ℝ (ℝ × ℝ) V₁ V₂ U h₁ h₂
  have hdiag : (1,1) ∈ V₂ := by simp [V₂, LinearMap.mem_ker]
  rw [← heq] at hdiag
  norm_num [V₁, LinearMap.mem_ker] at hdiag

#print axioms GroundTruth.linear_algebra_1C_23_certificate
