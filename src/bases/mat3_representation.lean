import ..fglib
import .invertible_mat3
import .linear_space3
import .representation

namespace FG

/- ## mat3 Representation -/

class mat3_representation {G : Type} [group G]
  (f : G → mat3) :=
( id_mapped  : f 1 = 1 )
( mul_mapped : ∀g₁ g₂, f g₁ * f g₂ = f (g₁ * g₂) )

namespace mat3_representation

variables {G : Type} [group G] 

/- `mat3_representation` is a `representation G ℝ vec3` -/
@[simps] instance representation (f : G → mat3)
  [mat3_representation f] : representation G ℝ vec3 :=
{ map := λg, (f g).linear_operator,
  id_mapped := by calc (f 1).linear_operator = (1 : mat3).linear_operator
      : by rw _inst_2.id_mapped
    ... = 1
      : begin
        apply linear_map.ext,
        intro x,
        cases' x,
        simp
      end,
  mul_mapped := begin
    intros g₁ g₂,
    apply linear_map.ext,
    intro x,
    cases' x,
    have t := _inst_2.mul_mapped,
    have h := t g₁ g₂,
    rw ←h,
    cases' (f g₁),
    cases' (f g₂),
    simp,
    repeat { apply and.intro },
    repeat { ring }
  end }

@[simp] def is_equivalent (f g: G → mat3) [mat3_representation f] [mat3_representation g] :
  ∃(A : invertible_mat3)

end mat3_representation

-- variables {R : Type*) (M : Type*)
--   [group G] [ring R] [add_comm_monoid M] [module R M]
-- @[simp] def representation : representation linear_mat3 ℝ vec3 :=
-- class representation (G : Type) [group G]
--   : representation G ℝ vec3 :=
-- ( f : G → mat3 )
-- ( id_mapped'  : f 1 = 1 )
-- ( mul_mapped' : ∀g₁ g₂, f g₁ * f g₂ = f (g₁ * g₂) )
-- ( map := λg, (f g).linear_operator )
-- ( id_mapped := by calc map 1 = (f 1).linear_operator
--     : refl
--   ... = (1 : mat3).linear_operator
--     : by apply id_mapped'
--   ... = 1
--     : by refl )
-- ( mul_mapped := by simp [mul_mapped'] )
--   -- representation G ℝ vec3 :=
-- { map := linear_operator,
--   id_mapped :=

-- /- Irreducible representations -/
-- namespace representation


-- /- Equivalent representations -/
-- -- def setoid : setoid (representation G R M) :=
-- -- { r := λa b, is_equivalent a b,
-- --   iseqv := sorry }
-- -- def is_irreducible (map : G → linear_operator R M) : Prop :=
-- --   ∀g₁ g₂, map g₁ * map g₂ = map (g₁ * g₂)

-- end mat3


end FG