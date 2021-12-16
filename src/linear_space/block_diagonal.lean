import ..fglib
import ..basic
import .vector
import .square_matrix

namespace FG

inductive block_diagonal : Type
| empty : block_diagonal
| block {n : ℕ} : square_matrix n → block_diagonal → block_diagonal

namespace block_diagonal

@[simp] def length : block_diagonal → ℕ
| empty := 0
| (block a b) := a.length + b.length

def to_func : block_diagonal → matrix_func
| empty _ _ := 0
| (block a b) i j := if i < a.length then
    if j < a.length then a i j else 0
  else
    if j < a.length then 0 else
      b.to_func (i - a.length) (j - a.length)

@[simp] def to_matrix (A : block_diagonal) :
  square_matrix (length A - 1)
| ⟨i, _⟩ ⟨j, _⟩ := A.to_func i j

@[simp] def to_matrix_n (A : block_diagonal) (n : ℕ) :
  square_matrix n
| ⟨i, _⟩ ⟨j, _⟩ := A.to_func i j

/- Have to reduce over block_diagonal instead of block_diagonal since the length is unknown-/
def reduce {α : Type} (f : α → block_diagonal → α)
  : α → block_diagonal → α
| x empty       := x
| x (block a b) := reduce (f x (block a b)) b

@[simp] def det (A : block_diagonal) : ℂ :=
  A.to_matrix.det

/- A block matrix's determinant is the product of determinants of all the blocks -/
@[simp] lemma block_det (A : block_diagonal) :
  A.det = A.reduce (λ(x B), match B with
    | empty       := x
    | (block a b) := x * a.det
  end) 1 :=
sorry

@[simp] def is_invertible (A : block_diagonal) : Prop :=
  A.to_matrix.is_invertible

/- A block matrix is invertible if and only if all the blocks are invertible -/
@[simp] lemma block_invertible (A : block_diagonal) :
  A.is_invertible ↔ A.reduce (λ(x B), match B with
    | empty       := x
    | (block a b) := x ∧ a.is_invertible
  end) true :=
begin
  rw iff_eq_eq,
  calc A.is_invertible = A.to_matrix.is_invertible
      : by refl
    ... = (A.to_matrix.det ≠ 0)
      : by rw square_matrix.det_ne_zero_iff 
    ... = (A.det ≠ 0)
      : by refl
    ... = (A.reduce (λ(x B), match B with
        | empty       := x
        | (block a b) := x * a.det
      end) 1 ≠ 0)
      : by rw block_det
    ... = A.reduce (λ(x B), match B with
        | empty       := x
        | (block a b) := x ∧ a.is_invertible
      end) true 
      : by sorry
end

end block_diagonal

end FG
