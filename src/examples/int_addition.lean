import ..fglib
import ..basic
import ..linear_space
import ..matrix_representation

namespace FG

/- ## Example : addition of integers -/

/- `ℤ` is a group under addition -/

namespace example_int

@[simp] def one : ℤ := 0
@[simp] def mul (a b : ℤ) : ℤ := a + b
@[simp] def inv (a : ℤ) : ℤ := -a

instance : group ℤ :=
{ one := one,
  mul := mul,
  inv := has_neg.neg,
  one_mul := by intro a; simp,
  mul_one := by intro a; simp,
  mul_assoc := by intros a b c; simp; ring,
  mul_left_inv := begin
    intro a,
    have h : mul (inv a) a = one := by simp,
    exact h
  end }

/- Here is a representation -/
def rep : matrix_representation 1 ℤ :=
{ f := λx, ⟨![![1, x], ![0, 1]], by square_matrix.invertible_det2⟩,
  id_mapped := begin
    apply invertible_matrix.ext,
    simp,
    rw ←matrix.diagonal_one,
    funext i j,
    fin_cases i,
    repeat { fin_cases j, repeat { refl } }
  end,
  mul_mapped := begin
    intros z₁ z₂,
    apply invertible_matrix.ext,
    simp,
  -- ⊢ ![![1, ↑z₁], ![0, 1]] * ![![1, ↑z₂], ![0, 1]] = ![![1, ↑(z₁ * z₂)], ![0, 1]]
    sorry
  end }


end example_int


end FG
