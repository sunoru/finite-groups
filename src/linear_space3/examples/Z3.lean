import ...fglib
import ...basic
import ...linear_space3

namespace FG

/- ## Example: Z₃

  The cyclic group of order 3

   \ | e | a | b |
  ----------------
   e | e | a | b |
   a | a | b | e |
   b | b | e | a |
-/
namespace example_Z₃

inductive Z₃ : Type
| e : Z₃
| a : Z₃
| b : Z₃

namespace Z₃

@[simp] def mul : Z₃ → Z₃ → Z₃
| x e := x
| e y := y
| a a := b
| a b := e
| b a := e
| b b := a

@[simp] def inv : Z₃ → Z₃
| e := e
| a := b
| b := a

@[simps] instance finite_group : finite_group Z₃ :=
{ one       := e,
  mul       := mul,
  mul_one   := by intro a; cases' a; refl,
  one_mul   := by intro a; cases' a; refl,
  mul_assoc :=
    by intros a b c; cases' a; cases' b; cases' c; refl,
  inv          := inv,
  mul_left_inv := by intro a; cases' a; refl,
  elems := ⟨ ⟦ [e, a, b] ⟧, by simp ⟩,
  complete := by intro x; cases' x; simp }

/- Z₃ is Abelian -/
@[simps] instance abelian : comm_group Z₃ :=
{ mul_comm :=
    by intros a b; cases' a; cases' b; refl,
  ..Z₃.finite_group }

/- A representation of Z₃ -/
noncomputable def rep1 : Z₃ → ℂ
| e := 1
| a := ⟨ -0.5,  real.sqrt 3 / 2 ⟩ -- exp(2πi/3)
| b := ⟨ -0.5, -real.sqrt 3 / 2 ⟩ -- exp(4πi/3)

noncomputable instance rep1.representation : representation Z₃ ℂ ℂ :=
{ map := λz, complex.to_linear_operator z.rep1,
  id_mapped := begin
    apply linear_map.ext,
    intro x,
    simp,
    calc e.rep1 * x = 1 * x
        : rfl
      ... = x
        : by rw one_mul
  end,
  mul_mapped := begin
    intros z₁ z₂,
    apply linear_map.ext,
    intro x,
    simp,
    cases' classical.em (x = 0),
    { apply or.intro_right, exact h },
    { apply or.intro_left,
      /- noncomputable since depends on ℂ * ℂ -/
      sorry }
  end }


/- ## The regular representation -/
def rep2 : Z₃ → mat3
| e := mat3.I
| a := ⟨ ⟨0, 0, 1⟩,
  ⟨1, 0, 0⟩,
  ⟨0, 1, 0⟩ ⟩
| b := ⟨ ⟨0, 1, 0⟩,
  ⟨0, 0, 1⟩,
  ⟨1, 0, 0⟩ ⟩

namespace rep2

/- The regular representation is a `mat3_representation`. -/
@[simps] instance representation : mat3_representation rep2 :=
{ id_mapped := by calc
    (1 : Z₃).rep2 = mat3.I
      : by refl,
  mul_mapped := begin
    intros g₁ g₂,
    cases' g₁,
    repeat { cases' g₂,
      repeat { simp [rep2, group.mul] } }
  end }

/- `P` is the projection operator of the invariant subspace -/
lemma is_reducible : mat3_representation.is_reducible rep2 :=
begin
  let P : mat3 :=
  ⟨ ⟨ 1/3, 1/3, 1/3 ⟩,
    ⟨ 1/3, 1/3, 1/3 ⟩,
    ⟨ 1/3, 1/3, 1/3 ⟩ ⟩,
  apply exists.intro P,
  intro x,
  cases' x,
  repeat { simp [rep2], ring }
end

end rep2

end Z₃

end example_Z₃

end FG
