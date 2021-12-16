import ..fglib
import ..basic
import ..linear_space
import ..matrix_representation

namespace FG

/- ## Example : Parity in quantum mechanics -/

namespace example_parity

/- Parity is the operation of reflection in a mirror.
  The corresponding group is called `ℤ₂`  -/

inductive ℤ₂ : Type
| e : ℤ₂
| p : ℤ₂

namespace ℤ₂ 

/- Reflecting twice gets you back to where you started. -/
@[simp] def mul : ℤ₂ → ℤ₂ → ℤ₂
| x e := x
| e y := y
| p p := e

@[simp] def inv : ℤ₂ → ℤ₂
| e := e
| p := p

/- `parity` is a group: -/
@[simps] instance : group ℤ₂ :=
{ mul := mul,
  one := e,
  inv := inv,
  one_mul := by intro x; cases' x; refl,
  mul_one := by intro x; cases' x; refl,
  mul_assoc := by intros a b c; cases' a; cases' b; cases' c; refl,
  mul_left_inv := by intro a; cases' a; refl }

@[simp] def rep_f : ℤ₂ → invertible_matrix 0
| e := ⟨![![ 1]], by square_matrix.invertible_det1⟩
| p := ⟨![![-1]], by square_matrix.invertible_det1⟩

def rep : matrix_representation 0 ℤ₂ :=
{ f := rep_f,
  id_mapped := begin
    apply invertible_matrix.ext,
    simp,
    funext i j,
    fin_cases i,
    fin_cases j,
    refl
  end,
  mul_mapped := begin
    intros z₁ z₂,
    apply invertible_matrix.ext,
    funext i j,
    fin_cases i,
    fin_cases j,
    cases' z₁,
    repeat { cases' z₂,
      repeat { simp [vec.smul] } }
  end }

end ℤ₂

end example_parity


end FG
