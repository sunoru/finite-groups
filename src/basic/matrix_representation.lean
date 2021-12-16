import ..fglib
import .finite_group
import .linear_space
import .representation

namespace FG

/-
  ## Matrix Representation
-/

/- `invertible_matrix` is a representation -/

class matrix_representation (n : ℕ) (G : Type) [finite_group G]
  extends representation G R (nvector n) :=
  (to_matrix : G → invertible_matrix n)
  (map := λx (to_matrix x).to_linear_operator)

end FG
