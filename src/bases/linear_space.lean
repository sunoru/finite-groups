import ..fglib
import .representation

namespace FG

/- General lemmas for vectors -/
-- section linear_space3

@[notation_class]
class has_dot (α : Type*) (β : Type*) (γ : Type*) := (dot : α → β → γ)

infixl ` ⬝ `:70  := has_dot.dot

structure vec3 :=
(x : ℝ)
(y : ℝ)
(z : ℝ)

namespace vec3

@[ext] theorem ext {a b : vec3} :
  a.x = b.x ∧ a.y = b.y ∧ a.z = b.z → a = b :=
begin
  intro h,
  cases' a,
  cases' b,
  simp at *,
  assumption
end

@[simps] def zero : vec3 := ⟨0, 0, 0⟩

@[simps] def add (a b : vec3) : vec3 :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

@[simps] def neg (a : vec3) : vec3 :=
  ⟨-a.x, -a.y, -a.z⟩

-- set_option trace.simplify.rewrite true
@[simps] instance add_comm_group : add_comm_group vec3 :=
{ zero := zero,
  add  := add,
  add_assoc := begin
    intros a b c,
    simp [add],
    repeat {apply and.intro},
    repeat {ring}
  end,
  zero_add := by intro a; ext; simp,
  add_zero := by intro a; ext; simp,
  add_comm := begin
    intros a b,
    /- `simp` could not directly work on `a + b = b + a`,
      but it could simplify `a.add b = b.add a` here,
      Similar case in some functions below such as `add_left_neg` -/
    have h : a.add b = b.add a := by simp [add]; repeat {apply and.intro}; repeat {ring},
    exact h
  end,
  neg := neg,
  add_left_neg := begin
    intro a,
    have h : (a.neg).add a = zero := by simp [add]; refl,
    exact h
  end }

def dot (a b : vec3) : ℝ :=
  a.x * b.x + a.y * b.y + a.z * b.z

-- lemma dot_zero

@[simps] instance has_dot : has_dot vec3 vec3 ℝ :=
{ dot := dot }

@[simp] def smul (c : ℝ) (v : vec3) : vec3 :=
  ⟨c * v.x, c * v.y, c * v.z⟩

@[simps] instance vector_space : module ℝ vec3 :=
{ smul := smul,
  one_smul := by intro b; ext; simp,
  mul_smul := begin
    intros x y b,
    simp,
    repeat {apply and.intro},
    repeat {ring}
  end,
  smul_zero := begin
    intro r,
    have h : smul r zero = 0 := by simp; refl,
    exact h
  end,
  zero_smul := begin
    intro r,
    have h : smul 0 r = 0 := by simp; refl,
    exact h
  end,
  smul_add := begin
    intros r x y,
    have h : smul r (x.add y) = (smul r x).add (smul r y) := begin
      simp [add],
      repeat {apply and.intro},
      repeat {ring},
    end,
    exact h
  end,
  add_smul := begin
    intros r s x,
    have h : smul (r + s) x = smul r x + smul s x := begin
      ext,
      simp [add],
      repeat {apply and.intro},
      repeat {ring_nf}
    end,
    exact h
  end }

end vec3

structure mat3 :=
(x : vec3)
(y : vec3)
(z : vec3)
-- (xx : ℝ) (xy : ℝ) (xz : ℝ)
-- (yx : ℝ) (yy : ℝ) (yz : ℝ)
-- (zx : ℝ) (zy : ℝ) (zz : ℝ)

namespace mat3

@[ext] theorem ext {a b : mat3} :
  a.x = b.x ∧ a.y = b.y ∧ a.z = b.z → a = b :=
begin
  intro h,
  cases' a,
  cases' b,
  simp at *,
  assumption
end

@[simps] def zero : mat3 := ⟨vec3.zero, vec3.zero, vec3.zero⟩

@[simps] def I : mat3 := ⟨
  ⟨1, 0, 0⟩,
  ⟨0, 1, 0⟩,
  ⟨0, 0, 1⟩
⟩

@[simps] def add (A B : mat3) : mat3 :=
  ⟨A.x + B.x, A.y + B.y, A.z + B.z⟩

@[simp] def neg (A : mat3) : mat3 :=
  ⟨-A.x, -A.y, -A.z⟩

@[simps] def col_x (A : mat3) : vec3 :=
  ⟨A.x.x, A.y.x, A.z.x⟩
@[simps] def col_y (A : mat3) : vec3 :=
  ⟨A.x.y, A.y.y, A.z.y⟩
@[simps] def col_z (A : mat3) : vec3 :=
  ⟨A.x.z, A.y.z, A.z.z⟩


@[simps] def mul (A B : mat3) : mat3 := ⟨
  ⟨A.x ⬝ B.col_x, A.x ⬝ B.col_y, A.x ⬝ B.col_z⟩,
  ⟨A.y ⬝ B.col_x, A.y ⬝ B.col_y, A.y ⬝ B.col_z⟩,
  ⟨A.z ⬝ B.col_x, A.z ⬝ B.col_y, A.z ⬝ B.col_z⟩
⟩

@[simps] instance ring : ring mat3 :=
{ zero := zero,
  add  := add,
  add_assoc := begin
    intros a b c,
    simp [add],
    repeat {apply and.intro},
    repeat {cc}
  end,
  zero_add := begin
    intro a,
    cases' a,
    simp [add, vec3.add],
    repeat {apply and.intro},
    /-
      Why `refl` cannot be directly used here? 
      ```
      invalid apply tactic, failed to unify
        {x := x.x, y := x.y, z := x.z} = x
      with
        ?m_2 = ?m_2
      ```
    -/
    { cases' x, refl },
    { cases' y, refl },
    { cases' z, refl }
  end,
  add_zero := begin
    intro a,
    cases' a,
    simp [add, vec3.add],
    repeat {apply and.intro},
    { cases' x, refl },
    { cases' y, refl },
    { cases' z, refl }
  end,
  add_comm := begin
    intros a b,
    have h : a.add b = b.add a := by simp [add]; repeat {apply and.intro}; repeat {cc},
    exact h
  end,
  neg := neg,
  add_left_neg := begin
    intro a,
    have h : (a.neg).add a = zero := by simp [add, vec3.add]; refl,
    exact h
  end,
  one := I,
  mul := mul,
  mul_assoc := begin
    intros a b c,
    simp [mul, vec3.dot],
    repeat {apply and.intro},
    /- This is the most time consuming step... -/
    repeat {ring},
  end,
  one_mul := begin
    intro a,
    cases' a,
    simp [mul, vec3.dot],
    repeat {apply and.intro},
    /-
      Why `refl` cannot be directly used here? 
      ```
      invalid apply tactic, failed to unify
        {x := x.x, y := x.y, z := x.z} = x
      with
        ?m_2 = ?m_2
      ```
    -/
    { cases' x, refl },
    { cases' y, refl },
    { cases' z, refl }
    -- repeat { ext, repeat {apply and.intro}, repeat {refl} },
  end,
  mul_one := begin
    intro a,
    cases' a,
    simp [mul, vec3.dot],
    repeat {apply and.intro},
    { cases' x, refl },
    { cases' y, refl },
    { cases' z, refl }
  end,
  left_distrib := begin
    intros a b c,
    simp [add, mul, vec3.dot, vec3.add],
    repeat {apply and.intro},
    repeat {ring}
  end,
  right_distrib := begin
    intros a b c,
    simp [add, mul, vec3.dot, vec3.add],
    repeat {apply and.intro},
    repeat {ring}
  end
}

@[simps] def mat_dot_vec (A : mat3) (x : vec3) : vec3 :=
  ⟨A.x ⬝ x, A.y ⬝ x, A.z ⬝ x⟩
@[simps] def vec_dot_mat (x : vec3) (A : mat3) : vec3 :=
  mat_dot_vec A x

@[simps] instance has_dot : has_dot mat3 vec3 vec3 :=
{ dot := mat_dot_vec }

lemma mat_dot_vec_assoc (A B : mat3) (v : vec3) :
  (A * B) ⬝ v = A.mat_dot_vec (B ⬝ v) :=
begin
  simp [mat_dot_vec, mul, vec3.dot],
  repeat {apply and.intro},
  repeat {ring}
end

@[simps] instance linear_space : module mat3 vec3 :=
{ smul := mat_dot_vec,
  one_smul := begin
    intros b,
    simp [mat_dot_vec, vec3.dot],
    cases' b,
    refl,
  end,
  mul_smul := mat_dot_vec_assoc,
  smul_add := begin
    intros r x y,
    simp [mat_dot_vec, vec3.dot, vec3.add],
    repeat {apply and.intro},
    repeat {ring}
  end,
  add_smul := begin
    intros r s x,
    simp [mat_dot_vec, vec3.dot, vec3.add],
    repeat {apply and.intro},
    repeat {ring},
  end,
  smul_zero := begin
    intro r,
    simp [mat_dot_vec, vec3.dot],
    refl
  end,
  zero_smul := begin
    intro r,
    simp [mat_dot_vec, vec3.dot],
    refl
  end }

@[simp] def linear_operator (A : mat3) : linear_operator mat3 vec3 :=
{ to_fun := λx, A ⬝ x,
  map_add' := begin
    intros x y,
    simp [mat_dot_vec, vec3.dot, vec3.add],
    repeat {apply and.intro},
    repeat {ring}
  end,
  map_smul' := begin
    intros B x,

    -- simp [mat_dot_vec, vec3.dot],
    -- repeat {apply and.intro},
    -- { ring_nf, },
    -- repeat {sorry}
  end }

lemma linear_operator_eq (A B : mat3) :
  A = B → linear_operator A = linear_operator B :=
begin
  intro h,
  apply linear_map.ext,
  intro x,
  simp,
  rw h
end

lemma I_eq_id : linear_operator I = linear_map.id :=
begin
  apply linear_map.ext,
  intro x,
  simp,
  cases' x,
  calc (⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩ : mat3) ⬝ (vec3.mk x y z)
    = vec3.mk ((vec3.mk 1 0 0) ⬝ (vec3.mk x y z))
      ((vec3.mk 0 1 0) ⬝ (vec3.mk x y z))
      ((vec3.mk 0 0 1) ⬝ (vec3.mk x y z))
      : by refl
    ... = vec3.mk (1 * x + 0 * y + 0 * z) (0 * x + 1 * y + 0 * z) (0 * x + 0 * y + 1 * z)
      : by refl
    ... = vec3.mk x y z
      : by norm_num,
end

lemma linear_operator_mul_linear_operator (A B : mat3) :
  linear_operator A * linear_operator B = linear_operator (A * B) :=
begin
  apply linear_map.ext,
  intro v,
  simp,
  apply (mat_dot_vec_assoc A B v).symm,
end

end mat3

-- end linear_space3

end FG
