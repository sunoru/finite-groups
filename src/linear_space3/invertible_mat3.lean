import ..fglib
import ..basic
import .data

namespace FG

/- ## Invertible 3x3 Matrix -/

namespace mat3

def is_invertible (A : mat3) : Prop :=
  ∃(B : mat3), A * B = 1

/- ### Unitary operator -/
@[simp] def is_unitary (A : mat3) : Prop :=
  A * A.transpose = 1

lemma unitary_is_inverible (A : mat3) :
  is_unitary A → is_invertible A :=
begin
  intro h,
  use A.transpose,
  assumption
end


noncomputable def inverse (A : mat3) : mat3 :=
begin
  let detA := A.det,
  let AT := A.transpose,
  let subdet := λ(a b c d : ℝ), a * d - b * c,
  let M : mat3 := ⟨
    ⟨subdet AT.y.y AT.y.z AT.z.y AT.z.z, subdet AT.y.x AT.y.z AT.z.x AT.z.z, subdet AT.y.x AT.y.y AT.z.x AT.z.y⟩,
    ⟨subdet AT.x.y AT.x.z AT.z.y AT.z.z, subdet AT.x.x AT.x.z AT.z.x AT.z.z, subdet AT.x.x AT.x.y AT.z.x AT.z.y⟩,
    ⟨subdet AT.x.y AT.x.z AT.y.y AT.y.z, subdet AT.x.x AT.x.z AT.y.x AT.y.z, subdet AT.x.x AT.x.y AT.y.x AT.y.y⟩
  ⟩,
  use ⟨
    ⟨M.x.x / detA, -M.x.y / detA, M.x.z / detA⟩,
    ⟨-M.y.x / detA, M.y.y / detA, -M.y.z / detA⟩,
    ⟨M.z.x / detA, -M.z.y / detA, M.z.z / detA⟩
  ⟩
end

@[simp] theorem exists_inverse (A : mat3) (h : A.det ≠ 0) :
  A * A.inverse = 1 :=
sorry

@[simp] lemma invertible_det_ne_zero (A : mat3) :
  is_invertible A → A.det ≠ 0 :=
begin
  intros ha,
  cases' ha with B hab,
  intro hn,
  have hadet0 : A.det = 0 := by simp [hn],
  have hdet0 : A.det * B.det = 0 := by rw hadet0; apply zero_mul B.det,
  have hdet := by calc A.det * B.det = (A * B).det
      : by rw mat3.det_mul_det
    ... = (1 : mat3).det
      : by rw hab
    ... = 1
      : by rw mat3.det_one,
  linarith
end

@[simp] lemma det_ne_zero_invertible (A : mat3) :
  A.det ≠ 0 → is_invertible A :=
begin
  intro h,
  use A.inverse,
  exact exists_inverse A h
end

theorem det_iff (A : mat3) :
  is_invertible A ↔ A.det ≠ 0 :=
begin
  split,
  { exact invertible_det_ne_zero A },
  { exact det_ne_zero_invertible A }
end

lemma mul_eq_one_assoc (A B : mat3) : A * B = 1 → B * A = 1 :=
begin
  intro h,
  sorry
end

lemma inverse_invertible (A : mat3) (h : A.det ≠ 0) :
  is_invertible A.inverse :=
begin
  apply exists.intro A,
  apply mul_eq_one_assoc,
  exact exists_inverse A h
end

end mat3

@[simp] def invertible_mat3 : Type := { A : mat3 // A.is_invertible }

namespace invertible_mat3

@[ext] theorem ext {A B : invertible_mat3} :
  A.val = B.val → A = B :=
subtype.eq

@[simps] def mul (A B : invertible_mat3) : invertible_mat3 :=
⟨A.val * B.val, begin
  apply mat3.det_ne_zero_invertible,
  have ha := mat3.invertible_det_ne_zero A.val A.property,
  have hb := mat3.invertible_det_ne_zero B.val B.property,
  calc (A.val * B.val).det = A.val.det * B.val.det
      : by rw mat3.det_mul_det
    ... ≠ 0
      : by apply mul_ne_zero ha hb
end⟩

@[simps] def one : invertible_mat3 :=
⟨1, by simp⟩

@[simps] noncomputable def inv (A : invertible_mat3) :
  invertible_mat3 :=
⟨A.val.inverse, begin
  apply mat3.inverse_invertible,
  apply mat3.invertible_det_ne_zero,
  exact A.property
end⟩


@[simp] lemma one_mul (A : invertible_mat3) :
  mul one A = A :=
begin
  cases' A,
  apply ext,
  simp only [one, mul],
  cases' val,
  simp,
  repeat { apply and.intro },
  { cases' x, refl },
  { cases' y, refl },
  { cases' z, refl }
end

@[simp] lemma mul_one (A : invertible_mat3) :
  mul A one = A :=
begin
  cases' A,
  cases' val,
  ext,
  simp,
  repeat { apply and.intro },
  { cases' x, refl },
  { cases' y, refl },
  { cases' z, refl }
end

@[simp] lemma mul_assoc (A B C : invertible_mat3) :
  mul (mul A B) C = mul A (mul B C) :=
begin
  cases' A with A _,
  cases' B with B _,
  cases' C with C _,
  ext,
  simp,
  repeat { apply and.intro },
  repeat { ring }
end

@[simp] lemma mul_left_inv (A : invertible_mat3) :
  mul (inv A) A = one :=
begin
  cases' A,
  apply ext,
  simp only [one, inv, mul],
  apply mat3.mul_eq_one_assoc,
  apply mat3.exists_inverse,
  apply mat3.invertible_det_ne_zero,
  assumption
end

@[simps] noncomputable instance group : group invertible_mat3 :=
{ mul := mul,
  one := one,
  inv := inv,
  one_mul := one_mul,
  mul_one := mul_one,
  mul_assoc := mul_assoc,
  mul_left_inv := mul_left_inv }

@[simps] def transpose (A : invertible_mat3) : invertible_mat3 :=
⟨A.val.transpose, begin
  apply mat3.det_ne_zero_invertible,
  rw mat3.transpose_det,
  apply mat3.invertible_det_ne_zero,
  exact A.property
end⟩

@[simp] def is_unitary (A : invertible_mat3) : Prop :=
  A.val.is_unitary

end invertible_mat3

end FG
