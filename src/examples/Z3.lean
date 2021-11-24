import ..fglib
import ..bases.finite_group
import ..bases.linear_space
import ..bases.representation

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
| e y := y
| x e := x
| a a := b
| a b := e
| b a := e
| b b := a

@[simp] def inv : Z₃ → Z₃
| e := e
| a := b
| b := a

instance finite_group : finite_group Z₃ :=
{ one       := e,
  mul       := mul,
  mul_one   := by intro a; cases' a; refl,
  one_mul   := by intro a; cases' a; refl,
  mul_assoc :=
    by intros a b c; cases' a; cases' b; cases' c; refl,
  inv          := inv,
  mul_left_inv := by intro a; cases' a; refl,
  elems := ⟨⟦[e, a, b]⟧, by simp⟩,
  complete := by intro x; cases' x; simp }

/- Z₃ is Abelian -/
instance abelian : comm_group Z₃ :=
{ mul_comm :=
    by intros a b; cases' a; cases' b; refl,
  ..Z₃.finite_group }

/- A representation of Z₃ -/
noncomputable def rep1 : Z₃ → ℂ
| e := 0
| a := ⟨-0.5,  real.sqrt 3 / 2⟩ -- exp(2πi/3)
| b := ⟨-0.5, -real.sqrt 3 / 2⟩ -- exp(4πi/3)

/- ## The regular representation -/
def rep2 : Z₃ → linear_operator mat3 vec3
| e := mat3.linear_operator mat3.I
| a := mat3.linear_operator ⟨
  ⟨0, 0, 1⟩,
  ⟨1, 0, 0⟩,
  ⟨0, 1, 0⟩
⟩
| b := mat3.linear_operator ⟨
  ⟨0, 1, 0⟩,
  ⟨0, 0, 1⟩,
  ⟨1, 0, 0⟩
⟩

instance rep2.representation : representation rep2 :=
{ id_mapped  := by calc
    (1 : Z₃).rep2 = mat3.linear_operator mat3.I
      : by refl
    ... = linear_map.id
      : mat3.I_eq_id
    ... = (1 : linear_operator mat3 vec3)
      : by refl,
  mul_mapped := begin
    intros g₁ g₂,
    cases' g₁,
    { calc e.rep2 * g₂.rep2 = mat3.I.linear_operator * g₂.rep2
        : by refl
      ... = g₂.rep2
        : by rw mat3.I_eq_id; apply one_mul g₂.rep2
      ... = (e * g₂).rep2
        : by cases' g₂; repeat {refl} },
    { sorry },
    { sorry }
    -- { cases' g₂,
    --   { calc e.rep2 * e.rep2 = mat3.I.linear_operator * mat3.I.linear_operator
    --       : by refl
    --     ... = mat3.I.linear_operator
    --       : by rw mat3.I_eq_id; refl
    --     ... = e.rep2
    --       : by refl
    --     ... = (e * e).rep2
    --       : by refl },
    --   { calc e.rep2 * a.rep2 = mat3.I.linear_operator * mat3.linear_operator
    --         ⟨ ⟨0, 0, 1⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩ ⟩
    --       : by refl
    --     ... = mat3.linear_operator ⟨ ⟨0, 0, 1⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩ ⟩
    --       : by rw mat3.I_eq_id; refl
    --     ... = a.rep2
    --       : by refl
    --     ... = (e * a).rep2
    --       : by refl },
    --   { calc e.rep2 * b.rep2 = mat3.I.linear_operator * mat3.linear_operator
    --         ⟨ ⟨0, 1, 0⟩, ⟨0, 0, 1⟩, ⟨1, 0, 0⟩ ⟩
    --       : by refl
    --     ... = mat3.linear_operator ⟨ ⟨0, 1, 0⟩, ⟨0, 0, 1⟩, ⟨1, 0, 0⟩ ⟩
    --       : by rw mat3.I_eq_id; refl
    --     ... = b.rep2
    --       : by refl
    --     ... = (e * b).rep2
    --       : by refl },
    -- }
    -- cases' x,
    -- cases' g₁,
    -- {
    --   cases' g₂,
    --   simp [rep2],
    -- }
  end }

end Z₃

end example_Z₃

end FG
