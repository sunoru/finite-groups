import ..fglib
import ..basic
import ..linear_space
import ..matrix_representation

namespace FG

/- ## Example: S₃

  The **permutation group** (or **symmetric group**) of 3 objects.

  A common notation of its elements is:
  - a₁ = (1, 2, 3)
  - a₂ = (3, 2, 1)
  - a₃ = (1, 2)
  - a₄ = (2, 3)
  - a₅ = (3, 1)

    \  | e  | a₁ | a₂ | a₃ | a₄ | a₅
  ------------------------------------
    e  | e  | a₁ | a₂ | a₃ | a₄ | a₅
    a₁ | a₁ | a₂ | e  | a₅ | a₃ | a₄
    a₂ | a₂ | e  | a₁ | a₄ | a₅ | a₃
    a₃ | a₃ | a₄ | a₅ | e  | a₁ | a₂
    a₄ | a₄ | a₅ | a₃ | a₂ | e  | a₁
    a₅ | a₅ | a₃ | a₄ | a₁ | a₂ | e
-/
namespace example_S₃

inductive S₃ : Type
| e  : S₃
| a₁ : S₃
| a₂ : S₃
| a₃ : S₃
| a₄ : S₃
| a₅ : S₃

namespace S₃

open square_matrix

@[simp] def mul : S₃ → S₃ → S₃
| x  e  := x
| e  y  := y
| a₁ a₁ := a₂
| a₁ a₂ := e
| a₁ a₃ := a₅
| a₁ a₄ := a₃
| a₁ a₅ := a₄
| a₂ a₁ := e
| a₂ a₂ := a₁
| a₂ a₃ := a₄
| a₂ a₄ := a₅
| a₂ a₅ := a₃
| a₃ a₁ := a₄
| a₃ a₂ := a₅
| a₃ a₃ := e
| a₃ a₄ := a₁
| a₃ a₅ := a₂
| a₄ a₁ := a₅
| a₄ a₂ := a₃
| a₄ a₃ := a₂
| a₄ a₄ := e
| a₄ a₅ := a₁
| a₅ a₁ := a₃
| a₅ a₂ := a₄
| a₅ a₃ := a₁
| a₅ a₄ := a₂
| a₅ a₅ := e

@[simp] def inv : S₃ → S₃
| e  := e
| a₁ := a₂
| a₂ := a₁
| a₃ := a₃
| a₄ := a₄
| a₅ := a₅

/- S₃ is a **finite group**. -/

@[simps] instance : finite_group S₃ :=
{ one       := e,
  mul       := mul,
  mul_one   := by intro a; cases' a; refl,
  one_mul   := by intro a; cases' a; refl,
  mul_assoc :=
    by intros a b c; cases' a; cases' b; cases' c; refl,
  inv          := inv,
  mul_left_inv := by intro a; cases' a; refl,
  elems := ⟨⟦[e, a₁, a₂, a₃, a₄, a₅]⟧, by simp⟩,
  complete := by intro x; cases' x; simp }

/- S₃ is a **transformation group** on a physical system. -/

/- S₃ is **non-Abelian**. i.e., the multiplication law is not commutative. -/
lemma is_non_abelian :
  ¬∀ a b : S₃, a * b = b * a :=
begin
  intro h,
  have h₂ : a₁ * a₃ ≠ a₃ * a₁ := by simp,
  apply h₂,
  apply h
end

/-
  A representation on a 2-dimensional vector space.
-/
@[simp] noncomputable def rep_func : S₃ → invertible_matrix 1
| e  := ⟨![
    ![1, 0],
    ![0, 1]
  ], by invertible_det2⟩
| a₁ := ⟨![
    ![         -1 / 2, -real.sqrt 3 / 2],
    ![real.sqrt 3 / 2, -1 / 2]
  ], by sorry⟩
| a₂ := ⟨![
    ![          -1 / 2, real.sqrt 3 / 2],
    ![-real.sqrt 3 / 2, -1 / 2]
  ], by sorry⟩
| a₃ := ⟨![
    ![-1, 0],
    ![ 0, 1]
], by invertible_det2⟩
| a₄ := ⟨![
    ![          1 / 2, real.sqrt 3 / 2],
    ![real.sqrt 3 / 2, -1 / 2]
  ], by sorry⟩
| a₅ := ⟨![
    ![           1 / 2, -real.sqrt 3 / 2],
    ![-real.sqrt 3 / 2, -1 / 2]
  ], by sorry⟩

@[simps] noncomputable def rep : matrix_representation 1 S₃ :=
{ f := rep_func,
  id_mapped := begin
    apply invertible_matrix.ext,
    simp [rep_func],
    rw ←matrix.diagonal_one,
    funext i j,
    fin_cases i,
    repeat { fin_cases j, repeat { refl } }
  end,
  mul_mapped := sorry }

/- It is a unitary irreducible representation. -/
example : rep.is_unitary :=
begin
  simp,
  intro z,
  cases' z,
  { simp,
    funext i j,
    fin_cases i,
    repeat { fin_cases j,
      repeat { simp [matrix.conj_transpose] } } },
  repeat { sorry }
end
example : rep.is_irreducible :=
begin
  sorry
end

end S₃

end example_S₃

end FG
