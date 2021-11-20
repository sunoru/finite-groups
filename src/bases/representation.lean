import ..fglib

namespace FG

/-
  ## Linear Operators

  `linear_operator` is a simplified version of `linear_map` in mathlib.

  It is defined on some field `α` and is an instance of monoid with composition operations.
-/
#check linear_map

def linear_operator (α : Type) [field α] := linear_map (ring_hom.id α) α α

namespace linear_operator

instance monoid {α : Type} [field α] : monoid (linear_operator α) :=
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

#check linear_operator ℝ

/- Representation -/
class representation {β : Type} (α : Type) [group α] [field β] :=
(map        : α → linear_operator β)
(id_mapped  : map 1 = 1)
(mul_mapped : ∀g₁ g₂, map g₁ * map g₂ = map (g₁ * g₂))

#check monoid

end FG
