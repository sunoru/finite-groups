import ..fglib
import data.pi

/-
  ## Square Matrix
-/

def square_matrix (n : ℕ) : Type := matrix (fin n) (fin n) ℂ

namespace square_matrix

variables {n : ℕ}

@[simps] instance ring : ring (square_matrix n) :=
{ zero := pi.has_zero.zero,
  add := pi.has_add.add,
  add_assoc := pi.add_group.add_assoc,
  zero_add := pi.add_group.zero_add,
  add_zero := pi.add_group.add_zero,
  add_comm := pi.add_comm_group.add_comm,
  neg := pi.has_neg.neg,
  add_left_neg := pi.add_group.add_left_neg,
  mul := matrix.mul,
  one := pi.has_one.one,
  mul_assoc := λA B C, matrix.mul_assoc A B C,
  one_mul := sorry,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry }

def is_invertible (A : square_matrix n) : Prop :=
  ∃ (B : square_matrix n), A * B = 1

end square_matrix

/-
  ## Matrix Representation
-/

class matrix_representation (n : ℕ) (G : Type) [group G]
  extends representation G vec :=
  (to_matrix : G → square_matrix n)
