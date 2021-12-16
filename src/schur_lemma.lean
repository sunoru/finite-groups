import .fglib
import .basic
import .linear_space
import .matrix_representation

namespace FG

/- ## Schur's lemma -/

open matrix_representation
open square_matrix
open invertible_matrix

/- If `D₁` and `D₂` are inequivalent, irreducible representations,
  and `∀g ∈ G, D₁(g) * A = A * D₂(g)`, then `A = 0` -/

namespace schur_lemma₁

variables{n : ℕ} (A : square_matrix n)

def vector_annihilates_right : Prop :=
  ∃(μ : vec n), A.mul_vec μ = 0

def vector_annihilates_left : Prop :=
  ∃(ν : vec n), A.transpose.mul_vec ν = 0

def vector_annihilates : Prop :=
  vector_annihilates_right A ∨ vector_annihilates_left A

lemma det_eq_zero_vector_annihilates :
  A.det = 0 ↔ vector_annihilates A :=
sorry

/- `A` is either annihilated by a vector on the left or on the right,
  otherwise it muse be an invertible matrix  -/
lemma vector_annihilates_or_ivertible :
  vector_annihilates A ∨ is_invertible A :=
begin
  rw ←det_eq_zero_vector_annihilates,
  rw ←det_ne_zero_iff,
  apply classical.em
end

lemma schur_lemma₁ {G : Type} [group G] 
    (D₁ D₂ : matrix_representation n G)
    (h_inequivalent : ¬is_equivalent D₁ D₂)
    (h_irreducible₁ : is_irreducible D₁)
    (h_irreducible₂ : is_irreducible D₂)
    (h : ∀(g : G), (D₁.f g).val * A = A * (D₂.f g).val) :
  A = 0 :=
begin
  cases' classical.em (is_invertible A) with h₁,
  { let AA : invertible_matrix n := ⟨A, h₁⟩,
    have hAA : AA.val = A := rfl,
    have h₂ : AA⁻¹ * AA = 1 := group.mul_left_inv _,
    have h₃ : AA⁻¹.val * AA.val = 1 :=
    begin
      cases' h₂,
      assumption
    end,
    have hg : ∀(g : G), (AA⁻¹).val * (D₁.f g).val * A = (D₂.f g).val :=
    begin
      intro g,
      calc (AA⁻¹).val * (D₁.f g).val * AA.val = (AA⁻¹).val * A * (D₂.f g).val
          : by rw [mul_assoc, h g, mul_assoc]
        ... = (D₂.f g).val
          : begin
            rw ←hAA,
            rw h₃,
            rw one_mul
          end
    end,
    apply false.elim,
    apply h_inequivalent,
    rw is_equivalent_iff,
    use AA,
    intro z,
    apply eq.symm,
    apply invertible_matrix.ext,
    apply hg z },
  { sorry }
end

end schur_lemma₁

end FG
