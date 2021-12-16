import ..fglib
import ..basic
import .vector

namespace FG

/-
  ## Square Matrix

  The basic definitions of mathlib's `matrix` are used.
  Assume all matrix elements are ℂ, which is commonly used in physics.
-/

def matrix_func : Type := ℕ → ℕ → ℂ

def square_matrix (n : ℕ) : Type := matrix (fin (n + 1)) (fin (n + 1)) ℂ

namespace square_matrix

variables {n : ℕ}

@[simp] def length : square_matrix n → ℕ := n + 1

@[simp] def to_func (A : square_matrix n) : matrix_func :=
  λ(i j : ℕ), if i < A.length ∧ j < A.length
    then A i j else 0

@[simps] instance : ring (square_matrix n) :=
{ zero := matrix.has_zero.zero,
  add := matrix.has_add.add,
  add_assoc := matrix.add_group.add_assoc,
  zero_add := matrix.add_group.zero_add,
  add_zero := matrix.add_group.add_zero,
  add_comm := matrix.add_comm_group.add_comm,
  neg := matrix.has_neg.neg,
  add_left_neg := matrix.add_group.add_left_neg,
  mul := matrix.has_mul.mul,
  one := matrix.has_one.one,
  mul_assoc := λA B C, matrix.mul_assoc A B C,
  one_mul := sorry,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry }

@[simp] def det (A : square_matrix n) : ℂ :=
  matrix.det A

@[simp] lemma det_one :
  det (1 : square_matrix n) = 1 :=
by simp

@[simp] lemma det_zero :
  det (0 : square_matrix n) = 0 :=
by simp


def is_invertible (A : square_matrix n) : Prop :=
  ∃ (B : square_matrix n), B * A = 1

@[simp] lemma square_eq_self (A : square_matrix n) :
  A * A = A → A = 0 ∨ A = 1 :=
begin
  intro h,
  sorry
end

lemma invertible_assoc (A B : square_matrix n) :
  A * B = 1 → B * A = 1 :=
begin
  intro h,
  have h₂ := by calc B * A = B * 1 * A
      : by rw mul_one B
    ... = B * (A * B) * A
      : by rw ←h
    ... = B * A * (B * A)
      : begin
      rw ←ring.mul_assoc,
      rw ring.mul_assoc,
      refl
    end,
  have h₃ := square_eq_self (B * A) h₂.symm,
  have h₄ := by calc A.det * B.det = (A * B).det
      : (matrix.det_mul A B).symm
    ... = (1 : square_matrix n).det
      : by rw h
    ... = (1 : ℂ)
      : det_one,
  cases' h₃,
  { apply false.elim,
    have h₅ : A.det * B.det ≠ 0 :=
      ne_zero_of_eq_one h₄,
    apply h₅,
    calc A.det * B.det = B.det * A.det
      : by cc
    ... = (B * A).det
      : by apply (matrix.det_mul B A).symm
    ... = (0 : square_matrix n).det
      : by rw h_1
    ... = (0 : ℂ)
      : by apply det_zero },
  { assumption }
end

/- There is a computable inverse matrix if det is not zero -/
@[simp] lemma det_ne_zero_invertible (A : square_matrix n) :
  A.det ≠ 0 → A.is_invertible :=
sorry

@[simp] lemma invertible_det_ne_zero (A : square_matrix n) :
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

@[simp] theorem det_ne_zero_iff (A : square_matrix n) :
  A.det ≠ 0 ↔ A.is_invertible :=
iff.intro (det_ne_zero_invertible A) (invertible_det_ne_zero A)

@[simp] def mul_vec (A : square_matrix n) (v : vec n) :
  vec n :=
A.mul_vec v

instance : module (square_matrix n) (vec n) :=
{ smul := mul_vec,
  one_smul := sorry,
  mul_smul := sorry,
  smul_zero := sorry,
  smul_add := sorry,
  zero_smul := sorry,
  add_smul := sorry }

@[simp] def to_linear_operator (A : square_matrix n) :
  linear_operator ℂ (vec n) :=
{ to_fun := λv, A.mul_vec v,
  map_add' := begin
    intros v w,
    apply vec.ext,
    intro i,
    simp [ matrix.mul_vec,
      matrix.dot_product, matrix.dot_product_add,
      mul_add, finset.sum_add_distrib ],
  end,
  map_smul' := begin
    intros a v,
    have h := (matrix.mul_vec_lin A).map_smul' a v,
    simp at h,
    simp [mul_vec],
    exact h,
  end }

@[simp] def conj_transpose (A : square_matrix n) : square_matrix n :=
  matrix.conj_transpose A

@[simp] lemma conj_transpose_det (A : square_matrix n) :
  A.conj_transpose.det = star A.det :=
by apply matrix.det_conj_transpose

@[simp] def is_unitary (A : square_matrix n) : Prop :=
  A.conj_transpose = A


@[simp] def det2 (A : square_matrix 1) : ℂ :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

/- Too complicated to prove this? -/
lemma det2_eq (A : square_matrix 1) :
  A.det = A.det2 :=
sorry

meta def invertible_det2 : tactic unit :=
do
  tactic.applyc `FG.square_matrix.det_ne_zero_invertible,
  `[simp [FG.square_matrix.det2_eq]]

end square_matrix

end FG
