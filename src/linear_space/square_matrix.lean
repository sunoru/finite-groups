import ..fglib
import ..basic
import .vector

namespace FG

/-
  ## Square Matrix

  The basic definitions of mathlib's `matrix` are used.
-/

def matrix_func : Type := ℕ → ℕ → ℂ

/- Note that a `square_matrix n` is a `(n+1) × (n+1)` matrix. -/
def square_matrix (n : ℕ) : Type := matrix (fin (n + 1)) (fin (n + 1)) ℂ

namespace square_matrix

variables {n : ℕ} (A : square_matrix n)

@[simp] def length : square_matrix n → ℕ := n + 1

@[simp] def to_func : matrix_func :=
  λ(i j : ℕ), if i < A.length ∧ j < A.length
    then A i j else 0

@[simp] def I : square_matrix n :=
  matrix.has_one.one

/- `square_matrix n` is a module -/
@[simps] instance : ring (square_matrix n) :=
{ ..matrix.ring }

/- `ℂ` is a module over `square_matrix` -/
instance : module ℂ (square_matrix n) :=
{ ..matrix.module }


@[simp] def mul_vec (v : vec n) :
  vec n :=
matrix.mul_vec A v

/- `square_matrix n` is a module over `vec n` -/
instance : module (square_matrix n) (vec n) :=
{ smul := mul_vec,
  one_smul := λv, by simp,
  mul_smul := λA B v, by simp,
  smul_zero := λA,
  begin
    funext i j,
    simp [matrix.mul_vec]
  end,
  smul_add := λA x y, by apply matrix.mul_vec_add,
  zero_smul := λx, by simp,
  add_smul := λA B x, by apply matrix.add_mul_vec, }

@[simp] def det : ℂ :=
  matrix.det A

@[simp] lemma det_one :
  det (1 : square_matrix n) = 1 :=
by simp

@[simp] lemma det_zero :
  det (0 : square_matrix n) = 0 :=
by simp

/- Finite nonzero dimensional matrices must have at least one eigenvalue/eigenvector. -/
@[simp] lemma has_nonzero_eigenvalue_and_eigenvector
  (h : A ≠ 0) :
  ∃ (x : ℂ) (v : vec n), x ≠ 0 ∧ v ≠ 0 ∧ (A - x • I).det = 0 ∧ (A - x • I) • v = 0 :=
sorry

def is_invertible : Prop :=
  ∃ (B : square_matrix n), B * A = 1

@[simp] def adjacent : ℂ :=
begin
end

@[simp] def inverse (h : A.det ≠ 0) : square_matrix n :=
  λ(i j), A.adjacent i j / A.det

/- There is a computable inverse matrix if det is not zero -/
@[simp] lemma det_ne_zero_invertible :
  A.det ≠ 0 → A.is_invertible :=
sorry

@[simp] lemma invertible_det_ne_zero :
  A.is_invertible → A.det ≠ 0 :=
begin
  intro h,
  cases' h with B,
  have hdet := by calc B.det * A.det = (B * A).det
      : (matrix.det_mul B A).symm
    ... = (1 : square_matrix n).det
      : by rw h
    ... = (1 : ℂ)
      : det_one,
  simp,
  intro hfalse,
  have h := right_ne_zero_of_mul_eq_one hdet,
  apply h,
  assumption
end

@[simp] theorem det_ne_zero_iff :
  A.det ≠ 0 ↔ A.is_invertible :=
iff.intro (det_ne_zero_invertible A) (invertible_det_ne_zero A)

@[simp] def to_linear_operator :
  linear_operator ℂ (vec n) :=
{ to_fun := λv, A.mul_vec v,
  map_add' :=
  begin
    intros v w,
    apply vec.ext,
    intro i,
    simp [ matrix.mul_vec,
      matrix.dot_product, matrix.dot_product_add,
      mul_add, finset.sum_add_distrib ],
  end,
  map_smul' :=
  begin
    intros a v,
    have h := (matrix.mul_vec_lin A).map_smul' a v,
    simp at h,
    simp [mul_vec],
    exact h,
  end }

@[simp] def transpose : square_matrix n :=
  matrix.transpose A

@[simp] lemma transpose_det :
  A.transpose.det = A.det :=
by apply matrix.det_transpose

@[simp] def conj_transpose : square_matrix n :=
  matrix.conj_transpose A

@[simp] lemma conj_transpose_det :
  A.conj_transpose.det = star A.det :=
by apply matrix.det_conj_transpose

@[simp] def is_unitary : Prop :=
  A.conj_transpose = A

@[simp] def det1 (A : square_matrix 0) : ℂ :=
  A 0 0

lemma det1_eq (A : square_matrix 0) :
  A.det = A.det1 :=
by simp

meta def invertible_det1 : tactic unit :=
do
  tactic.applyc `FG.square_matrix.det_ne_zero_invertible,
  `[simp [FG.square_matrix.det1_eq]]

@[simp] def det2 (A : square_matrix 1) : ℂ :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

/- This was copied from mathlib's internal file :( -/
lemma det2_eq (A : square_matrix 1) :
  A.det = A.det2 :=
begin
  simp [matrix.det_succ_row_zero, fin.sum_univ_succ],
  ring,
end

/- Helper tactic for quickly solve simple 2-dimensional determinants. -/
meta def invertible_det2 : tactic unit :=
do
  tactic.applyc `FG.square_matrix.det_ne_zero_invertible,
  `[simp [FG.square_matrix.det2_eq]]

end square_matrix

end FG
