import ..fglib
import .finite_group
import .linear_space
import .representation

namespace FG

/-
  ## Matrix Representation
-/

/-
  `invertible_matrix` (**genearal linear group**) is a
  **representation** of a **group** `G` in matrix form,
  on a **vector space** `V` over the **field** `ℂ`.
 -/

class matrix_representation (n : ℕ) (G : Type) [finite_group G]
  extends representation G ℂ (vec n) :=
  (to_matrix : G → invertible_matrix n)
  (map := λ(x : G), (to_matrix x).to_linear_operator)

end FG
