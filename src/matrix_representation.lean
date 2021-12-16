import .fglib
import .basic
import .linear_space

namespace FG

/-
  ## Matrix Representation
-/

/-
  `invertible_matrix` (**genearal linear group**) is a
  **representation** of a **group** `G` in matrix form,
  on a **vector space** `V` over the **field** `ℂ`.
 -/

structure matrix_representation (n : ℕ) (G : Type) [finite_group G] :=
(f          : G → invertible_matrix n)
(id_mapped  : f 1 = 1 )
(mul_mapped : ∀z₁ z₂, f z₁ * f z₂ = f (z₁ * z₂) )

namespace matrix_representation

variables {n : ℕ} {G : Type} [finite_group G]

@[ext] theorem ext (D D' : matrix_representation n G) :
  D.f = D'.f → D = D' :=
begin
  intro h,
  cases' D with D,
  cases' D' with D',
  simp at *,
  exact h
end

@[simps] instance (D : matrix_representation n G) : representation G ℂ (vec n) :=
{ map := λ(x : G), (D.f x).to_linear_operator,
  id_mapped := begin
    cases' D,
    apply linear_map.ext,
    intro x,
    simp [id_mapped]
  end,
  mul_mapped := begin
    cases' D,
    intros z₁ z₂,
    apply linear_map.ext,
    intro x,
    simp *,
    have h := mul_mapped z₁ z₂,
    simp [invertible_matrix.mul] at h,
    have h₂ := iff.elim_left subtype.ext_iff_val h,
    simp at h₂,
    rw ←h₂,
    refl
  end }

/- ## Equivalent Representations -/

@[simp] def is_equivalent (D D' : matrix_representation n G) : Prop :=
  ∃(A : invertible_matrix n), ∀(z : G), D.f z = A.inv * (D'.f z) * A

@[simp] def is_unitary (D : matrix_representation n G) : Prop :=
  ∀(z : G), (D.f z).is_unitary

/- ## Reducible Representations -/

/- **Similarity Transformation** is noncomputable because it depends on 
  the group inv lemmas.-/
@[simp] noncomputable def similarity_transformation
    (D : matrix_representation n G) (S : invertible_matrix n)
  : matrix_representation n G :=
{ f := λ(z : G), S⁻¹ * (D.f z) * S,
  id_mapped := begin
    cases' D,
    simp only [id_mapped],
    rw mul_one,
    rw mul_left_inv
  end,
  mul_mapped := begin
    cases' D,
    intros z₁ z₂,
    simp only,
    rw ←mul_mapped,
    calc S⁻¹ * f z₁ * S * (S⁻¹ * f z₂ * S) = S⁻¹ * f z₁ * (S * S⁻¹) * f z₂ * S
        : begin
          rw ←mul_assoc,
          rw ←mul_assoc,
          rw mul_assoc _ S S⁻¹
        end
      ... = S⁻¹ * f z₁ * 1 * f z₂ * S
        : by rw mul_right_inv
      ... = S⁻¹ * f z₁ * f z₂ * S
        : by rw mul_one
      ... = S⁻¹ * (f z₁ * f z₂) * S
        : by rw mul_assoc S⁻¹ _ _
  end }

@[simp] def is_reducible (D : matrix_representation n G) : Prop :=
  ∃(P : invertible_matrix n), ∀(x : G), P * (D.f x) * P = (D.f x) * P

@[simp] def is_irreducible (D : matrix_representation n G) : Prop :=
  ¬ is_reducible D

def direct_sum {n₁ : ℕ} {n₂ : ℕ}
  (D₁ : matrix_representation n₁ G) (D₂ : matrix_representation n₂ G) :
  matrix_representation (n₁ + n₂ + 1) G :=
{ f := λ(z : G), block (D₁.f z) (D₂.f z),
  id_mapped := sorry,
  mul_mapped := sorry }

def block_diagonal_form (D : matrix_representation n G) : Prop :=
  

@[simp] def is_completely_reducible (D : matrix_representation n G) : Prop :=
  ∃(D' : invertible_matrix n), D.is_equivalent D' ∧ D.is_diagonal

end matrix_representation

end FG