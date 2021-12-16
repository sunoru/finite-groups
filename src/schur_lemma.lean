import .fglib
import .basic
import .linear_space
import .matrix_representation

namespace FG

/- ## Schur's lemma -/

open matrix_representation
open invertible_matrix

theorem schur_lemma {G : Type} [group G] {n : ℕ}
    (D₁ D₂ : matrix_representation n G)
    (h_inequivalent : ¬is_equivalent D₁ D₂)
    (h_irreducible₁ : is_irreducible D₁)
    (h_irreducible₂ : is_irreducible D₂)
    (A : square_matrix n)
    (h : ∀(g : G), (D₁.f g).val * A = A * (D₂.f g).val) :
  A = 0 :=
begin
sorry
end


end FG
