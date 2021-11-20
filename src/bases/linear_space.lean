import ..fglib
import .representation

namespace FG

/- General lemmas for vectors -/
section linear_space3

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
  add_comm := sorry,
  neg := neg,
  /- TODO: ? -/
  add_left_neg := sorry }

def dot (a b : vec3) : ℝ :=
  a.x * b.x + a.y * b.y + a.z * b.z

notation a `⬝` b := dot a b

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
  ⟨A.x ⬝ A.col_x, A.x ⬝ A.col_y, A.x ⬝ A.col_z⟩,
  ⟨A.y ⬝ A.col_x, A.y ⬝ A.col_y, A.y ⬝ A.col_z⟩,
  ⟨A.z ⬝ A.col_x, A.z ⬝ A.col_y, A.z ⬝ A.col_z⟩
⟩

instance ring : ring mat3 :=
{ zero := zero,
  add  := add,
  add_assoc := sorry,
  zero_add := begin
    intro a,
    ext,
    simp,
    ext,
    repeat {apply and.intro},
    repeat {ring}
  end, -- by intro a; ext; simp,
  add_zero := begin
    intro a,
    ext,
    simp,
    ext,
    repeat {apply and.intro},
    repeat {ring}
  end,
  add_comm := sorry,
  neg := neg,
  add_left_neg := sorry,
  one := I,
  mul := mul,
  mul_assoc := sorry,
  one_mul := sorry,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
}

def linear_operator (A : mat3) : linear_operator mat3 :=
{ to_fun := λB, A * B,
  map_add' := sorry,
  map_smul' := sorry }

end mat3

end linear_space3

end FG
