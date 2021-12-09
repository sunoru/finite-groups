import ..fglib
import .representation

namespace FG

/- General lemmas for vectors -/
-- section linear_space3

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

@[simp] def zero : vec3 := ⟨0, 0, 0⟩

@[simp] def add (a b : vec3) : vec3 :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

@[simp] def neg (a : vec3) : vec3 :=
  ⟨-a.x, -a.y, -a.z⟩

-- set_option trace.simplify.rewrite true
@[simp] instance add_comm_group : add_comm_group vec3 :=
{ zero := zero,
  add  := add,
  add_assoc := begin
    intros a b c,
    simp,
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
    have h : a.add b = b.add a := by simp; repeat {apply and.intro}; repeat {ring},
    exact h
  end,
  neg := neg,
  add_left_neg := begin
    intro a,
    have h : (a.neg).add a = zero := by simp; repeat {apply and.intro}; repeat {ring},
    exact h
  end }

@[simp] def dot (a b : vec3) : ℝ :=
  a.x * b.x + a.y * b.y + a.z * b.z

instance has_dot : has_dot vec3 vec3 ℝ :=
{ dot := dot }

@[simp] def smul (c : ℝ) (v : vec3) : vec3 :=
  ⟨c * v.x, c * v.y, c * v.z⟩

instance vector_space : module ℝ vec3 :=
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
    have h : smul r (x.add y) = (smul r x).add (smul r y) := by simp; repeat {apply and.intro}; repeat {ring},
    exact h
  end,
  add_smul := begin
    intros r s x,
    have h : smul (r + s) x = smul r x + smul s x := by simp; repeat {apply and.intro}; repeat {ring_nf},
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

@[simp] def zero : mat3 := ⟨vec3.zero, vec3.zero, vec3.zero⟩

@[simp] def I : mat3 := ⟨
  ⟨1, 0, 0⟩,
  ⟨0, 1, 0⟩,
  ⟨0, 0, 1⟩
⟩

@[simp] def add (A B : mat3) : mat3 :=
  ⟨A.x + B.x, A.y + B.y, A.z + B.z⟩

@[simp] def neg (A : mat3) : mat3 :=
  ⟨-A.x, -A.y, -A.z⟩

@[simp] def col_x (A : mat3) : vec3 :=
  ⟨A.x.x, A.y.x, A.z.x⟩
@[simp] def col_y (A : mat3) : vec3 :=
  ⟨A.x.y, A.y.y, A.z.y⟩
@[simp] def col_z (A : mat3) : vec3 :=
  ⟨A.x.z, A.y.z, A.z.z⟩

@[simp] def mul (A B : mat3) : mat3 := ⟨
  ⟨vec3.dot A.x B.col_x, vec3.dot A.x B.col_y, vec3.dot A.x B.col_z⟩,
  ⟨vec3.dot A.y B.col_x, vec3.dot A.y B.col_y, vec3.dot A.y B.col_z⟩,
  ⟨vec3.dot A.z B.col_x, vec3.dot A.z B.col_y, vec3.dot A.z B.col_z⟩
⟩

/-
  Similar problem.
  The following does not work with `simp [vec3.dot]`
 -/
-- @[simp] def mul (A B : mat3) : mat3 := ⟨
--   ⟨A.x ⬝ B.col_x, A.x ⬝ B.col_y, A.x ⬝ B.col_z⟩,
--   ⟨A.y ⬝ B.col_x, A.y ⬝ B.col_y, A.y ⬝ B.col_z⟩,
--   ⟨A.z ⬝ B.col_x, A.z ⬝ B.col_y, A.z ⬝ B.col_z⟩
-- ⟩

instance ring : ring mat3 :=
{ zero := zero,
  add  := add,
  add_assoc := begin
    intros a b c,
    simp,
    repeat {apply and.intro},
    repeat {cc}
  end,
  zero_add := begin
    intro a,
    ext,
    simp,
    ext,
    repeat {apply and.intro},
    repeat {ring}
  end,
  add_zero := begin
    intro a,
    ext,
    simp,
    ext,
    repeat {apply and.intro},
    repeat {ring}
  end,
  add_comm := begin
    intros a b,
    have h : a.add b = b.add a := by simp; repeat {apply and.intro}; repeat {cc},
    exact h
  end,
  neg := neg,
  add_left_neg := begin
    intro a,
    have h : (a.neg).add a = zero := by simp; refl,
    exact h
  end,
  one := I,
  mul := mul,
  mul_assoc := begin
    intros a b c,
    simp,
    repeat {apply and.intro},
    repeat {cc},
  end,
  one_mul := begin
    intro a,
    simp,
    repeat {apply and.intro},
    repeat {cc},
    -- intro a,
    -- simp,
  end,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
}

@[simp] def mat_dot_vec (A : mat3) (x : vec3) : vec3 :=
  ⟨A.x ⬝ x, A.y ⬝ x, A.z ⬝ x⟩
@[simp] def vec_dot_mat (x : vec3) (A : mat3) : vec3 :=
  mat_dot_vec A x

instance has_dot : has_dot mat3 vec3 vec3 :=
{ dot := mat_dot_vec }
instance has_dot₂ : has_dot vec3 mat3 vec3 :=
{ dot := vec_dot_mat }

lemma mat_dot_vec_assoc (A B : mat3) (v : vec3) :
  A.mat_dot_vec (B ⬝ v) = (A * B) ⬝ v :=
sorry

instance linear_space : module mat3 vec3 :=
{ smul := mat_dot_vec,
  one_smul := sorry,
  mul_smul := sorry,
  smul_add := sorry,
  smul_zero := sorry,
  add_smul := sorry,
  zero_smul := sorry }

@[simp] def linear_operator (A : mat3) : linear_operator mat3 vec3 :=
{ to_fun := λx, A ⬝ x,
  map_add' := sorry,
  map_smul' := sorry }

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
  apply mat_dot_vec_assoc
end

end mat3

-- end linear_space3

end FG
