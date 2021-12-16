import ..fglib
import .representation

namespace FG

/- ## Vector -/

def vec (n : ℕ) := (fin (n + 1) → ℂ)  -- := vector ℂ (n + 1)

namespace vec

variables {n : ℕ}

-- @[simp] def to_func (v : vec n) (i : fin (n + 1)) : ℂ :=
-- vector.nth v i

-- @[simp] def from_func (f : fin (n + 1) → ℂ) : vec n :=
-- vector.of_fn f

@[ext] theorem ext (v w : vec n) :
  (∀(i : fin (n + 1)), v i = w i) → v = w :=
funext
-- vector.ext

@[simp] def zero : vec n :=
  λ_, 0
-- vector.repeat 0 (n + 1)

@[simp] def add (v w : vec n) : vec n :=
  λi, v i + w i
-- vector.map₂ (+) v w

/-
  ~Notes: Is there a better way to do this..?~ 
-/
@[simp] lemma mapped₂_nth (f : ℂ → ℂ → ℂ) (v w : vec n) :
  -- ∀(i : fin (n + 1)), (vector.map₂ f v w).nth i = f (v.nth i) (w.nth i) :=
  ∀(i : fin (n + 1)), (vector.map₂ f v w).nth i = f (v.nth i) (w.nth i) :=
begin
  intro i,
  induction' n,
  { fin_cases i,
    cases' v with v hv,
    cases' w with w hw,
    cases' v with v₀,
    { contradiction },
    { cases' w with w₀,
      { contradiction },
      { simp [vector.nth, vector.map₂] }}
  },
  {
    -- cases' i with i hi,
    -- cases' v with v hv,
    -- cases' w with w hw,
    -- cases' v with v₀,
    -- { contradiction },
    -- { cases' w with w₀,
    --   { contradiction },
    --   { cases' i,
    --     { simp [vector.nth, vector.map₂] },
    --     { simp [vector.nth, vector.map₂],
    --       } } }
    sorry
  }
end

@[simps] instance : add_comm_monoid (vec n) :=
{ zero := zero,
  add := add,
  add_assoc := begin
    intros a b c,
    apply ext,
    intro i,
    calc vector.nth ((a.add b).add c) i = vector.nth (a.add b) i + vector.nth c i
        : by apply mapped₂_nth
      ... = vector.nth a i + vector.nth b i + vector.nth c i
        : by rw add; rw mapped₂_nth (+) a b
      ... = vector.nth a i + vector.nth (b.add c) i
        : by rw [add, mapped₂_nth (+) b c, add_assoc]
      ... = vector.nth (a.add (b.add c)) i
        : (mapped₂_nth (+) a (b.add c) i).symm
  end,
  zero_add := begin
    intro a,
    apply ext,
    intro i,
    simp,
  end,
  add_zero := begin
    intro a,
    apply ext,
    intro i,
    simp,
  end,
  add_comm := begin
    intros a b,
    apply ext,
    intro i,
    calc vector.nth (a.add b) i = a.nth i + b.nth i
        : by apply mapped₂_nth
      ... = b.nth i + a.nth i
        : by rw add_comm
      ... = (b.add a).nth i
        : by rw [add, mapped₂_nth (+) b a]
  end }

def smul (c : ℂ) (v : vec n) : vec n :=
  vector.map (λx, c * x) v

@[simps] instance : module ℂ (vec n) :=
{ smul := smul,
  smul_zero := begin
    intro a,
    apply ext,
    simp [smul]
  end,
  smul_add := begin
    intros a v w,
    apply ext,
    intro i,
    simp [smul],
    ring
  end,
  zero_smul := begin
    intro v,
    apply ext,
    simp [smul]
  end,
  one_smul := begin
    intro v,
    apply ext,
    simp [smul]
  end,
  add_smul := begin
    intros a v w,
    apply ext,
    intro i,
    simp [smul],
    ring
  end,
  mul_smul := begin
    intros a v w,
    apply ext,
    intro i,
    simp [smul],
    ring
  end }

end vec



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


@[simp] def mul_vec (A : square_matrix n) (v : vec n) :
  vec n :=
vec.from_func (A.mul_vec (v.to_func))

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
    simp [ matrix.mul_vec, vec.to_func,
      matrix.dot_product, matrix.dot_product_add,
      mul_add, finset.sum_add_distrib ]
  end,
  map_smul' := begin
    intros a v,
    apply vec.ext,
    intro i,
    have h := matrix.dot_product_smul a (A i) v.to_func,
    simp [matrix.mul_vec, vec.to_func, matrix.dot_product_smul,
      mul_add],
    sorry
  end }


end square_matrix

/-
  ## Invertible Matrix
-/
def invertible_matrix (n : ℕ) :=
  { A : square_matrix n // A.is_invertible }
  -- {A : square_matrix n // A.det ≠ 0}

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

end FG
