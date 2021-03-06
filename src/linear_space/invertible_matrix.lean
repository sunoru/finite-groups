import ..fglib
import ..basic
import .vector
import .square_matrix

namespace FG

/-
  ## Invertible Matrix

  Defined as a subtype of `square_matrix`.
-/
def invertible_matrix (n : ℕ) :=
  { A : square_matrix n // A.is_invertible }
-- Alternative:
  -- {A : square_matrix n // A.det ≠ 0}

namespace invertible_matrix

variables {n : ℕ} (A : invertible_matrix n)

@[ext] theorem ext (A B : invertible_matrix n) :
  A.val = B.val → A = B :=
begin
  intro h,
  cases' A with A,
  cases' B with B,
  simp at *,
  exact h
end

@[simp] def det : ℂ := A.val.det

@[simp] lemma det_ne_zero :
  A.det ≠ 0 :=
A.val.invertible_det_ne_zero A.property

-- /-
--   I used to se `classical.some` to get the inverse matrix.
--   It was actually computable but too complicated to implement here.
--   So were the definitions of `group` and `similarity_transformation` (in `matrix_representation`), etc.
--  -/
-- @[simp] noncomputable def inv (A : invertible_matrix n) :
--   invertible_matrix n :=
-- begin
--   cases' A with A,
--   let B := classical.some property,
--   have hB := classical.some_spec property,
--   have h : ∃A, A * B = 1 := begin
--     use A,
--     have h₁ : B * A = 1 → A * B = 1 := sorry,
--     rw h₁,
--     -- rw square_matrix.inv_assoc B A,
--     exact hB
--   end,
--   use ⟨B, h⟩
-- end

/- Now just use `A.val.inverse (A.det ≠ 0)` -/
@[simp] noncomputable def inv (A : invertible_matrix n) :
  invertible_matrix n :=
⟨ A.val.inverse A.det_ne_zero,
  begin
    let invA := A.val.inverse A.det_ne_zero,
    apply square_matrix.det_ne_zero_invertible,
    have h : A.val.det ≠ 0 := A.det_ne_zero,
    have h₂ := by calc invA.det * A.val.det = (invA * A.val).det
        : (matrix.det_mul invA A.val).symm
      ... = (1 : square_matrix n).det
        : by rw A.val.mul_inverse_left
      ... ≠ 0
        : by simp,
    have h₃ : invA.det ≠ 0 := (ne_zero_and_ne_zero_of_mul h₂).left,
    exact h₃
  end ⟩

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

@[simps] def I : invertible_matrix n := one

@[simp] protected lemma mul_left_inv :
  A.inv.mul A = one :=
begin
  apply ext,
  apply A.val.mul_inverse_left,
  apply A.val.invertible_det_ne_zero,
  exact A.property
end

/-
  This group of `n×n` invertible matrices is called
  **General Linear Group** over the field of complex numbers,
  and is a complex **Lie Group** of complex dimention `n²`.
-/
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
    simp
  end,
  inv := inv,
  mul_left_inv := invertible_matrix.mul_left_inv }

@[simp] def mul_vec (v : vec n) :
  vec n :=
A.val.mul_vec v

/- `invertible_matrix` is not a `ring`, which means it is not a `module` over `vec n`. -/

@[simp] def to_linear_operator :
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
    have h := (matrix.mul_vec_lin A.val).map_smul' a v,
    simp at h,
    simp [mul_vec],
    exact h,
  end }

@[simps] def conj_transpose : invertible_matrix n :=
⟨A.val.conj_transpose, begin
  apply square_matrix.det_ne_zero_invertible,
  rw square_matrix.conj_transpose_det,
  simp,
  apply square_matrix.invertible_det_ne_zero,
  exact A.property
end⟩

@[simp] def is_unitary : Prop :=
  A.val.is_unitary

end invertible_matrix


end FG
