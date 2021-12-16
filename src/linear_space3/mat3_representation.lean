import ..fglib
import ..basic
import .invertible_mat3
import .data

namespace FG

/- ## mat3 Representation -/

class mat3_representation {G : Type} [group G]
  (D : G → mat3)
  :=
( id_mapped  : D 1 = 1 )
( mul_mapped : ∀g₁ g₂, D g₁ * D g₂ = D (g₁ * g₂) )

namespace mat3_representation

variables {G : Type} [finite_group G]

/- `mat3_representation` is a `representation G ℝ vec3` -/
@[simps] instance representation (D : G → mat3)
  [mat3_representation D] : representation G ℝ vec3 :=
{ map := λx, (D x).to_linear_operator,
  id_mapped := by calc (D 1).to_linear_operator = (1 : mat3).to_linear_operator
      : by rw _inst_2.id_mapped
    ... = 1
      : begin
        apply linear_map.ext,
        intro x,
        cases' x,
        simp
      end,
  mul_mapped := begin
    intros x₁ x₂,
    apply linear_map.ext,
    intro x,
    cases' x,
    have t := _inst_2.mul_mapped,
    have h := t x₁ x₂,
    rw ←h,
    cases' (D x₁),
    cases' (D x₂),
    simp,
    repeat { apply and.intro },
    repeat { ring }
  end }


/- ## Equivalent Representations -/
@[simp] def is_equivalent (D D' : G → mat3) [mat3_representation D] [mat3_representation D'] : Prop :=
  ∃(A : invertible_mat3), ∀(x : G), D x = A.inv.val * (D' x) * A.val

@[simp] def is_unitary (D : G → mat3) [mat3_representation D] : Prop :=
  ∀(x : G), (D x).is_unitary

/- ## Reducible Representations -/
@[simp] def is_reducible (D : G → mat3) [mat3_representation D] : Prop :=
  ∃(P : mat3), ∀(x : G), P * (D x) * P = (D x) * P

@[simp] def is_irreducible (D : G → mat3) [mat3_representation D] : Prop :=
  ¬ is_reducible D

-- @[simp]
-- @[simp] def is_completely_reducible (D : G → mat3) [mat3_representation D] : Prop :=
--     ∃(Q )
--   ∃(P : mat3), ∀(x : G), P * (D x) * P = (D x) * P ∧ P * P = 1

end mat3_representation


end FG