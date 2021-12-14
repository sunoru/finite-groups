import ..fglib
import .representation

namespace FG

/- General lemmas for vectors -/
-- section linear_space3

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

/-
  `vec3` is equivalent to `vector ℝ 3`.
  We can firstly define the latter as a setoid
-/
def to_vector (v : vec3) : vector ℝ 3
:= ⟨[v.x, v.y, v.z], by refl ⟩
def from_vector (v : vector ℝ 3) : vec3
:= ⟨v.nth 1, v.nth 2, v.nth 3⟩


@[simp] def zero : vec3 := ⟨0, 0, 0⟩

@[simp] def add (a b : vec3) : vec3 :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

@[simp] def neg (a : vec3) : vec3 :=
  ⟨-a.x, -a.y, -a.z⟩

-- set_option trace.simplify.rewrite true
@[simps] instance add_comm_group : add_comm_group vec3 :=
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
    have h : (a.neg).add a = zero := by simp; refl,
    exact h
  end }

@[simp] def dot (a b : vec3) : ℝ :=
  a.x * b.x + a.y * b.y + a.z * b.z

infixr ` ⋅ `:100 := dot

-- lemma dot_zero

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
      simp,
      repeat {apply and.intro},
      repeat {ring},
    end,
    exact h
  end,
  add_smul := begin
    intros r s x,
    have h : smul (r + s) x = smul r x + smul s x := begin
      ext,
      simp,
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
  ⟨A.x.dot B.col_x, A.x.dot B.col_y, A.x.dot B.col_z⟩,
  ⟨A.y.dot B.col_x, A.y.dot B.col_y, A.y.dot B.col_z⟩,
  ⟨A.z.dot B.col_x, A.z.dot B.col_y, A.z.dot B.col_z⟩
⟩

@[simps] instance ring : ring mat3 :=
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
    cases' a,
    simp,
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
    simp,
    repeat {apply and.intro},
    { cases' x, refl },
    { cases' y, refl },
    { cases' z, refl }
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
    /- This is the most time consuming step... -/
    repeat {ring},
  end,
  one_mul := begin
    intro a,
    cases' a,
    simp,
    repeat {apply and.intro},
    { cases' x, refl },
    { cases' y, refl },
    { cases' z, refl }
    -- repeat { ext, repeat {apply and.intro}, repeat {refl} },
  end,
  mul_one := begin
    intro a,
    cases' a,
    simp,
    repeat {apply and.intro},
    { cases' x, refl },
    { cases' y, refl },
    { cases' z, refl }
  end,
  left_distrib := begin
    intros a b c,
    simp,
    repeat {apply and.intro},
    repeat {ring}
  end,
  right_distrib := begin
    intros a b c,
    simp,
    repeat {apply and.intro},
    repeat {ring}
  end }

@[simp] def mat_dot_vec (A : mat3) (x : vec3) : vec3 :=
  ⟨A.x.dot x, A.y.dot x, A.z.dot x⟩

lemma mat_dot_vec_assoc (A B : mat3) (v : vec3) :
  (A * B).mat_dot_vec v = A.mat_dot_vec (B.mat_dot_vec v) :=
begin
  simp,
  repeat {apply and.intro},
  repeat {ring}
end

@[simps] instance module_vec3 : module mat3 vec3 :=
{ smul := mat_dot_vec,
  one_smul := begin
    intros b,
    simp,
    cases' b,
    refl,
  end,
  mul_smul := mat_dot_vec_assoc,
  smul_add := begin
    intros r x y,
    simp,
    repeat {apply and.intro},
    repeat {ring}
  end,
  add_smul := begin
    intros r s x,
    simp,
    repeat {apply and.intro},
    repeat {ring},
  end,
  smul_zero := by intro r; simp,
  zero_smul := by intro r; simp }

@[simp] def linear_operator (A : mat3) : linear_operator ℝ vec3 :=
{ to_fun := λx, A • x,
  map_add' := begin
    intros x y,
    simp,
    repeat {apply and.intro},
    repeat {ring}
  end,
  map_smul' := begin
    intros B x,
    simp,
    repeat {apply and.intro},
    repeat {ring},
  end }

@[simp] lemma linear_operator_eq (A B : mat3) :
  A = B → linear_operator A = linear_operator B :=
begin
  intro h,
  apply linear_map.ext,
  intro x,
  simp [h]
end

@[simp] lemma I_eq_id : linear_operator I = linear_map.id :=
begin
  apply linear_map.ext,
  intro x,
  cases' x,
  simp
end

@[simp] lemma linear_operator_mul_linear_operator (A B : mat3) :
  linear_operator A * linear_operator B = linear_operator (A * B) :=
begin
  apply linear_map.ext,
  intro v,
  cases' v,
  simp,
  repeat {apply and.intro},
  repeat {ring}
end

@[simp] def transpose (A : mat3) : mat3 :=
  ⟨⟨A.x.x, A.y.x, A.z.x⟩,
   ⟨A.x.y, A.y.y, A.z.y⟩,
   ⟨A.x.z, A.y.z, A.z.z⟩⟩

@[simp] def det (A : mat3) : ℝ :=
  A.x.x * (A.y.y * A.z.z - A.y.z * A.z.y) -
  A.x.y * (A.y.x * A.z.z - A.y.z * A.z.x) +
  A.x.z * (A.y.x * A.z.y - A.y.y * A.z.x)

@[simp] lemma det_mul_det (A B : mat3) :
  det (A * B) = det A * det B :=
by simp; ring

@[simp] lemma det_one :
  det 1 = 1 :=
by simp

@[simp] lemma det_zero :
  det 0 = 0 :=
by simp

end mat3

-- end linear_space3

end FG