import ..fglib
import ..basic
import ..linear_space
import ..matrix_representation

namespace FG

/- ## Example : addition of integers -/

/- `ℤ` is a group under addition -/

namespace example_int

structure group_int : Type :=
( x : ℤ )

namespace group_int

-- @[simps] instance : has_coe int group_int :=
-- { coe := λ x, { x := x } }
-- @[simps] instance : has_coe group_int int :=
-- { coe := λ x, x.x }

@[simp] def one : group_int := { x := int.zero }
@[simp] def mul (a b : group_int) : group_int := { x := int.add a.x b.x }
@[simp] def inv (a : group_int) : group_int := { x := int.neg a.x }

@[ext] theorem ext (a b : group_int) : a.x = b.x → a = b :=
begin
  intro h,
  cases' a with a,
  cases' b with b,
  simp at h,
  rw h
end

@[simp] lemma ext_iff (a b : group_int) : a.x = b.x ↔ a = b :=
iff.intro (ext a b) (by intro h; rw h)

instance : group group_int :=
{ one := one,
  mul := mul,
  inv := inv,
  one_mul := by intro a; cases' a; simp; refl,
  mul_one := by intro a; cases' a; simp; refl,
  mul_assoc := by intros a b c; simp; ring,
  mul_left_inv := begin
    intro a,
    have h : mul (inv a) a = one := begin
      cases' a,
      simp,
      apply int.add_group.add_left_neg
    end,
    exact h
  end }

/- Here is a representation -/
def rep : matrix_representation 1 group_int :=
{ f := λx, ⟨![![1, x.x], ![0, 1]], by square_matrix.invertible_det2⟩,
  id_mapped := begin
    apply invertible_matrix.ext,
    simp,
    rw ←matrix.diagonal_one,
    funext i j,
    fin_cases i,
    repeat { fin_cases j, repeat { refl } }
  end,
  mul_mapped := begin
    intros z₁ z₂,
    apply invertible_matrix.ext,
    simp only [invertible_matrix.mul, invertible_matrix.group_mul],
    cases' z₁ with x,
    cases' z₂ with y,
    have h : ({x := x} : group_int) * {x := y} = {x := x + y} := by refl,
    rw h,
    funext i j,
    fin_cases i,
    { fin_cases j,
      { simp [vec.smul] },
      { simp [vec.smul, add_comm] } },
    { fin_cases j,
      { simp [vec.smul] },
      { simp [vec.smul] }
    }
  end }

/- The representation is reducible -/
@[simp] def P : square_matrix 1 := ![![1, 0], ![0, 0]]

lemma rep.is_reducible_by_P :
  rep.is_reducible_by P :=
begin
  intro x,
  cases' x,
  funext i j,
  fin_cases i,
  repeat { fin_cases j,
    repeat { simp [rep, vec.smul] } }
end

example : rep.is_reducible :=
begin
  use P,
  exact rep.is_reducible_by_P
end

/- But it is not completely reducible -/
example : ¬rep.is_completely_reducible :=
begin
  intro h,
  have h₁ := rep.orthogonal_completely_reducible P h rep.is_reducible_by_P,
  have h₂ : ¬rep.is_reducible_by (1 - P) :=
  begin
    apply iff.elim_right not_forall,
    use ⟨2⟩,
    have h₁ : (1 - P) = ![![0, 0], ![0, 1]] :=
    begin
      funext i j,
      fin_cases i,
      repeat { fin_cases j,
        repeat { simp [matrix.vec_head, matrix.vec_tail] } }
    end,
    have h₂ : (rep.f ⟨2⟩).val = ![![1, 2], ![0, 1]] :=
    begin
      simp [rep],
      funext i j,
      fin_cases i,
      repeat { fin_cases j, 
        repeat { simp } }
    end,
    have h₃ := by calc (1 - P) * (rep.f ⟨2⟩).val * (1 - P) = ![![0, 0], ![0, 1]] * ![![1, 2], ![0, 1]] * ![![0, 0], ![0, 1]]
        : by rw [h₁, h₂]
      ... = ![![0, 0], ![0, 1]]
        : begin
          funext i j,
          repeat { fin_cases j,
            repeat { simp [vec.smul, matrix.vec_head, matrix.vec_tail] } }
        end,
    have h₄ : (rep.f ⟨2⟩).val * (1 - P) = ![![0, 2], ![0, 1]] :=
      begin
        simp [rep],
        funext i j,
        repeat { fin_cases j,
          repeat { simp [vec.smul, matrix.vec_head, matrix.vec_tail] } }
      end,
    rw [h₃, h₄],
    intro h₅,
    apply_fun (λx, x 0 1) at h₅,
    simp at h₅,
    exact h₅
  end,
  exact h₂ h₁
end

end group_int

end example_int


end FG
