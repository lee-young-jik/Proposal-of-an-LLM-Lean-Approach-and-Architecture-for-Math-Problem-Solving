import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_7B_5_certificate :
¬ (
∀ T : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3),
  (∃ b : Module.Basis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)), ∀ i j, i ≠ j → LinearMap.toMatrix b b T i j = 0) →
  T.comp (LinearMap.adjoint T) = (LinearMap.adjoint T).comp T
) := by
  classical
  push_neg
  let A : Matrix (Fin 3) (Fin 3) ℂ := ![![1,1,0],![0,2,0],![0,0,3]]
  let P : Matrix (Fin 3) (Fin 3) ℂ := ![![1,1,0],![0,1,0],![0,0,1]]
  let Q : Matrix (Fin 3) (Fin 3) ℂ := ![![1,-1,0],![0,1,0],![0,0,1]]
  let D : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1,2,3]
  have hmul (M N : Matrix (Fin 3) (Fin 3) ℂ) : Matrix.toEuclideanLin (M*N) = (Matrix.toEuclideanLin M).comp (Matrix.toEuclideanLin N) := by
    apply LinearMap.ext
    intro x
    change WithLp.toLp 2 (Matrix.mulVec (M*N) (WithLp.ofLp x)) = WithLp.toLp 2 (Matrix.mulVec M (Matrix.mulVec N (WithLp.ofLp x)))
    rw [Matrix.mulVec_mulVec]
  have hone : Matrix.toEuclideanLin (1 : Matrix (Fin 3) (Fin 3) ℂ) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change WithLp.toLp 2 (Matrix.mulVec (1 : Matrix (Fin 3) (Fin 3) ℂ) (WithLp.ofLp x)) = x
    simp
  have hPQ : P*Q=1 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [P,Q,Matrix.mul_apply,Fin.sum_univ_succ]
  have hQP : Q*P=1 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [P,Q,Matrix.mul_apply,Fin.sum_univ_succ]
  have hAP : A*P=P*D := by
    ext i j
    change (A*P) i j = (P*Matrix.diagonal ![1,2,3] : Matrix (Fin 3) (Fin 3) ℂ) i j
    rw [Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> norm_num [A,P,Matrix.mul_apply,Fin.sum_univ_succ]
  let e : EuclideanSpace ℂ (Fin 3) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 3) := LinearEquiv.ofLinear (Matrix.toEuclideanLin P) (Matrix.toEuclideanLin Q)
    (by rw [← hmul,hPQ,hone]) (by rw [← hmul,hQP,hone])
  let E : Module.Basis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)) := (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis
  let b := E.map e
  let T := Matrix.toEuclideanLin A
  have hmat : LinearMap.toMatrix E E (Matrix.toEuclideanLin D) = D := by
    change LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis (Matrix.toEuclideanLin D) = D
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  have hDb (j : Fin 3) : Matrix.toEuclideanLin D (E j) = ((j.val:ℂ)+1) • E j := by
    apply E.repr.injective
    ext i
    have hc : (E.repr (Matrix.toEuclideanLin D (E j))) i = D i j := by rw [← LinearMap.toMatrix_apply,hmat]
    rw [hc]
    simp only [map_smul,Module.Basis.repr_self,Finsupp.smul_apply,Finsupp.single_apply,smul_eq_mul]
    by_cases hi : i=j
    · subst i; fin_cases j <;> norm_num [D,Matrix.diagonal,Fin.ext_iff]
    · simp [D,Matrix.diagonal,hi,Ne.symm hi]
  have hcomp : T.comp e.toLinearMap = e.toLinearMap.comp (Matrix.toEuclideanLin D) := by
    change (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin P) = (Matrix.toEuclideanLin P).comp (Matrix.toEuclideanLin D)
    rw [← hmul,← hmul,hAP]
  have hev (j : Fin 3) : T (b j) = ((j.val:ℂ)+1) • b j := by
    change T (e (E j)) = ((j.val:ℂ)+1) • e (E j)
    have hc := congrArg (fun L : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) => L (E j)) hcomp
    simpa only [LinearMap.comp_apply,hDb,map_smul] using hc
  refine ⟨T,⟨b,?_⟩,?_⟩
  · intro i j hij
    rw [LinearMap.toMatrix_apply,hev]
    simp only [map_smul,Module.Basis.repr_self,Finsupp.smul_apply,Finsupp.single_apply,smul_eq_mul,if_neg (Ne.symm hij),mul_zero]
  · intro hn
    have hadj : LinearMap.adjoint T = Matrix.toEuclideanLin A.conjTranspose := (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
    rw [hadj] at hn
    change (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin A.conjTranspose) = (Matrix.toEuclideanLin A.conjTranspose).comp (Matrix.toEuclideanLin A) at hn
    rw [← hmul,← hmul] at hn
    have hm := Matrix.toEuclideanLin.injective hn
    have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) hm
    norm_num [A,Matrix.mul_apply,Fin.sum_univ_succ] at h00

#print axioms GroundTruth.linear_algebra_7B_5_certificate
