import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_2B_8_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V],
  ∀ (v : Fin 4 → V) (U : Submodule F V),
  LinearIndependent F v → Submodule.span F (Set.range v) = ⊤ →
  v 0 ∈ U → v 1 ∈ U → v 2 ∉ U → v 3 ∉ U →
  LinearIndependent F (fun i : Fin 2 => v (Fin.castLE (by decide) i)) ∧
  Submodule.span F (Set.range (fun i : Fin 2 => v (Fin.castLE (by decide) i))) = U
) := by
  classical
  intro h
  let v : Fin 4 → (Fin 4 → ℝ) := Pi.basisFun ℝ (Fin 4)
  let ℓ : (Fin 4 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2 - LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3
  let U : Submodule ℝ (Fin 4 → ℝ) := LinearMap.ker ℓ
  have hv : LinearIndependent ℝ v := by
    simpa only [v] using (Pi.basisFun ℝ (Fin 4)).linearIndependent
  have hs : Submodule.span ℝ (Set.range v) = ⊤ := by
    simpa only [v] using (Pi.basisFun ℝ (Fin 4)).span_eq
  have h0 : v 0 ∈ U := by simp [U, ℓ, v, Pi.basisFun_apply, LinearMap.mem_ker]
  have h1 : v 1 ∈ U := by simp [U, ℓ, v, Pi.basisFun_apply, LinearMap.mem_ker]
  have h2 : v 2 ∉ U := by simp [U, ℓ, v, Pi.basisFun_apply, LinearMap.mem_ker]
  have h3 : v 3 ∉ U := by simp [U, ℓ, v, Pi.basisFun_apply, LinearMap.mem_ker]
  have heq := (h ℝ (Fin 4 → ℝ) v U hv hs h0 h1 h2 h3).2
  have hle : Submodule.span ℝ (Set.range (fun i : Fin 2 => v (Fin.castLE (by decide) i))) ≤
      LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    fin_cases i <;> simp [v, Pi.basisFun_apply, LinearMap.mem_ker]
  have hw : v 2 + v 3 ∈ U := by simp [U, ℓ, v, Pi.basisFun_apply, LinearMap.mem_ker]
  rw [← heq] at hw
  have hz := hle hw
  norm_num [v, Pi.basisFun_apply, LinearMap.mem_ker, Pi.single_apply, Fin.ext_iff] at hz

#print axioms GroundTruth.linear_algebra_2B_8_certificate
