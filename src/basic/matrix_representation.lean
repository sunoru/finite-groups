import ..fglib
import .representation
import .linear_space

namespace FG

/-
  ## Matrix Representation
-/

/- `invertible_matrix` is a representation -/

class matrix_representation (n : ℕ) (G : Type) [group G]
  extends representation G ℂ (nvector n) :=
  (to_matrix : G → invertible_matrix n)

end FG
