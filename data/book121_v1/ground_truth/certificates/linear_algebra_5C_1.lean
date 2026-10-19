import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_5C_1_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ T : V →ₗ[F] V, (∃ n : ℕ, ∃ b : Module.Basis (Fin n) F V, ∀ i j : Fin n, j < i → LinearMap.toMatrix b b (T.comp T) i j = 0) → (∃ n : ℕ, ∃ b : Module.Basis (Fin n) F V, ∀ i j : Fin n, j < i → LinearMap.toMatrix b b T i j = 0)
) := by
  intro h
  let T : ℂ →ₗ[ℝ] ℂ :=
    Complex.reLm.smulRight Complex.I - Complex.imLm.smulRight (1 : ℂ)
  have hT_sq : T.comp T = -(LinearMap.id : ℂ →ₗ[ℝ] ℂ) := by
    ext z
    apply Complex.ext <;> simp [T]
  have htri_sq :
      ∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℝ ℂ,
        ∀ i j : Fin n, j < i →
          LinearMap.toMatrix b b (T.comp T) i j = 0 := by
    refine ⟨2, Complex.orthonormalBasisOneI.toBasis, ?_⟩
    intro i j hij
    rw [hT_sq]
    simp only [map_neg, LinearMap.toMatrix_id, Matrix.neg_apply, Matrix.one_apply, if_neg (ne_of_gt hij), neg_zero]
  obtain ⟨n, b, hb⟩ := h ℝ ℂ T htri_sq
  have hn : n = 2 := by
    have he := Module.finrank_eq_card_basis b
    simpa only [Complex.finrank_real_complex,Fintype.card_fin] using he.symm
  subst n
  have h10 := hb (1 : Fin 2) (0 : Fin 2) (by decide)
  rw [LinearMap.toMatrix_apply] at h10
  let a : ℝ := (b.repr (T (b (0 : Fin 2)))) (0 : Fin 2)
  have heig : T (b (0 : Fin 2)) = a • b (0 : Fin 2) := by
    apply b.repr.injective
    ext i
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    fin_cases i
    · norm_num [a,Fin.ext_iff]
    · norm_num [a,h10,Fin.ext_iff]
  have hcalc : T (T (b (0 : Fin 2))) = (a * a) • b (0 : Fin 2) := by
    rw [heig, map_smul, heig, smul_smul]
  have hneg : T (T (b (0 : Fin 2))) = -b (0 : Fin 2) := by
    have hz := DFunLike.congr_fun hT_sq (b (0 : Fin 2))
    simpa using hz
  have hz : (a * a + 1) • b (0 : Fin 2) = 0 := by
    rw [add_smul, one_smul, ← hcalc, hneg]
    simp
  have ha : a * a + 1 = 0 := by
    rcases smul_eq_zero.mp hz with ha | hv
    · exact ha
    · exact False.elim (b.ne_zero (0 : Fin 2) hv)
  nlinarith [sq_nonneg a]

#print axioms GroundTruth.linear_algebra_5C_1_certificate
