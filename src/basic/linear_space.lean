import ..fglib
import data.pi

namespace FG
/-
  ## Square Matrix

  The basic definitions of mathlib's `matrix` are used.
  Assume all matrix elements are ℂ, which is commonly used in physics.
-/

def square_matrix (n : ℕ) : Type := matrix (fin (n + 1)) (fin (n + 1)) ℂ

namespace square_matrix

variables {n : ℕ}

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

end square_matrix

/-
  ## Invertible Matrix
-/
def invertible_matrix (n : ℕ) :=
  { A : square_matrix n // A.is_invertible }
  -- {A : square_matrix n // A.det ≠ 1}

namespace invertible_matrix

variables {n : ℕ}

@[ext] theorem ext (A B : invertible_matrix n) :
  A.val = B.val → A = B :=
begin
  intro h,
  cases' A with A,
  cases' B with B,
  simp at *,
  exact h
end

/-
  Use classical.some to get the inverse matrix.
  It's actually computable but too complicated to implement here.
 -/
@[simp] noncomputable def inv (A : invertible_matrix n) :
  invertible_matrix n :=
begin
  cases' A with A,
  let B := classical.some property,
  have hB := classical.some_spec property,
  have h : ∃A, A * B = 1 := begin
    apply exists.intro A,
    rw square_matrix.invertible_assoc B A,
    exact hB
  end,
  use ⟨B, h⟩
end

@[simp] lemma det_ne_zero (A : invertible_matrix n) :
  A.val.det ≠ 0 :=
A.val.invertible_det_ne_zero A.property

@[simp] lemma mul_invertible (A B : invertible_matrix n) :
  (A.val * B.val).is_invertible :=
square_matrix.det_ne_zero_invertible (A.val * B.val) (by calc
  (A.val * B.val).det = A.val.det * B.val.det
    : matrix.det_mul A.val B.val
  ... ≠ (0 : ℂ)
    : mul_ne_zero (det_ne_zero A) (det_ne_zero B))

@[simps] def mul (A B : invertible_matrix n) : invertible_matrix n :=
  ⟨A.val * B.val, mul_invertible A B⟩

@[simps] def one : invertible_matrix n :=
  ⟨1, (1 : square_matrix n).det_ne_zero_invertible
    (ne_zero_of_eq_one square_matrix.det_one)⟩

@[simps] noncomputable instance : group (invertible_matrix n) :=
{ mul := mul,
  one := one,
  mul_assoc := λA B C, begin
    apply ext,
    simp,
    apply square_matrix.ring.mul_assoc
  end,
  one_mul := begin
    intro a,
    apply ext,
    simp [square_matrix.ring.one_mul]
  end,
  mul_one := begin
    intro a,
    apply ext,
    simp,
    apply square_matrix.ring.mul_one
  end,
  inv := inv,
  mul_left_inv := begin
    intro A,
    let B := inv A,
    calc mul (inv A) A = mul B A
      : by refl
    ... = one
      : sorry
  end }

end invertible_matrix

def nvector (n : ℕ) : Type := vector ℂ (n + 1)

namespace nvector

variables {n : ℕ}

def to_func (v : nvector n) : fin n → ℂ
| i := vector.nth v i

instance : add_comm_monoid (nvector n) :=
sorry

instance : module (square_matrix n) (nvector n) :=
{ smul := matrix.mul_vec to_func}
-- { add_smul := begin
--     sorry
--   end,
--   zero_smul := begin
--     sorry
--   end }

end nvector

end FG
