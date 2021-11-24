import ..fglib

namespace FG

/-
  ## Linear Operators

  `linear_operator` is a simplified version of `linear_map` in mathlib.

  It is defined on some ring `α` and is an instance of monoid with composition operations.
-/
#check linear_map

def linear_operator (R : Type*) (M : Type*) [ring R] [add_comm_monoid M] [module R M] := linear_map (ring_hom.id R) M M

namespace linear_operator

variables {R : Type*} {M : Type*} [ring R] [add_comm_monoid M] [module R M]

instance monoid : monoid (linear_operator R M) :=
{ one := linear_map.id,
  mul := λf g, f.comp g,
  mul_one := by intro f; simp,
  one_mul := by intro f; simp,
  mul_assoc := begin
    intros f g h,
    simp,
    apply linear_map.comp_assoc
  end
}

end linear_operator

/- Representation -/
class representation {G : Type} {R : Type*} {M : Type*}
  [group G] [ring R] [add_comm_monoid M] [module R M]
  (map : G → linear_operator R M) :=
(id_mapped  : map 1 = 1)
(mul_mapped : ∀g₁ g₂, map g₁ * map g₂ = map (g₁ * g₂))

#check monoid

end FG
