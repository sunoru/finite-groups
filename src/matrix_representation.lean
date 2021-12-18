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

structure matrix_representation (n : ℕ) (G : Type) [group G] :=
(f          : G → invertible_matrix n)
(id_mapped  : f 1 = 1 )
(mul_mapped : ∀z₁ z₂, f z₁ * f z₂ = f (z₁ * z₂) )

namespace matrix_representation

variables {n : ℕ} {G : Type} [group G]
  (D : matrix_representation n G)

@[ext] theorem ext (D D' : matrix_representation n G) :
  D.f = D'.f → D = D' :=
begin
  intro h,
  cases' D with D,
  cases' D' with D',
  simp at *,
  exact h
end

@[simps] instance : has_coe (matrix_representation n G) (G → invertible_matrix n) :=
{ coe := matrix_representation.f }

@[simps] instance : has_coe_to_fun (matrix_representation n G) (λ_, G → invertible_matrix n) :=
{ coe := λD, D.f }

@[simps] instance : representation G ℂ (vec n) :=
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
    rw ←h₂
  end }

/- ## Equivalent Representations -/

@[simp] def is_equivalent (D D' : matrix_representation n G) : Prop :=
  ∃(A : invertible_matrix n), ∀(z : G), D.f z = A⁻¹ * (D'.f z) * A

lemma is_equivalent_symm (D D' : matrix_representation n G) :
  is_equivalent D D' → is_equivalent D' D :=
begin
  intro h,
  cases' h,
  use w⁻¹,
  intro z,
  rw h z,
  rw mul_assoc,
  rw mul_assoc,
  rw mul_right_inv,
  rw ←mul_assoc,
  rw ←mul_assoc,
  rw mul_left_inv,
  rw one_mul,
  rw mul_one
end

lemma is_equivalent_iff (D D' : matrix_representation n G) :
  is_equivalent D D' ↔ is_equivalent D' D :=
iff.intro (is_equivalent_symm D D') (is_equivalent_symm D' D)

@[simp] def is_unitary : Prop :=
  ∀(z : G), (D.f z).is_unitary

/- ## Reducible Representations -/

/- **Similarity Transformation** is noncomputable because it depends on
  the group inv lemmas.-/
@[simp] noncomputable def similarity_transformation
     (S : invertible_matrix n)
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

@[simp] def is_reducible_by (P : square_matrix n) : Prop :=
  ∀(x : G), P * (D.f x).val * P = (D.f x).val * P

@[simp] def is_reducible : Prop :=
  ∃(P : square_matrix n), is_reducible_by D P

@[simp] def is_irreducible : Prop :=
  ¬is_reducible D

def is_block_diagonal : Prop :=
  ∀z, ∃(A : block_diagonal), A.length - 1 = n → (D.f z).val = A.to_matrix_n n

@[simp] def is_completely_reducible : Prop :=
  ∃(D' : matrix_representation n G), is_equivalent D D' ∧ is_block_diagonal D'

@[simp] lemma orthogonal_completely_reducible
    (P : square_matrix n) (h : D.is_completely_reducible) :
  D.is_reducible_by P → D.is_reducible_by (1 - P) :=
sorry

noncomputable def irreducible_representation (h : D.is_completely_reducible)
  : matrix_representation n G :=
classical.some h

end matrix_representation

end FG