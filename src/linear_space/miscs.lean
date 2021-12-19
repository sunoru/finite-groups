import ..fglib
import ..basic
import .vector
import .square_matrix
import .invertible_matrix

namespace FG

/- Useful lemmas -/

namespace miscs

open square_matrix
open invertible_matrix

variables {n : ℕ} (A : square_matrix n)

def vector_annihilates_right : Prop :=
  ∃(μ : vec n), μ ≠ 0 ∧ A • μ = 0

def vector_annihilates_left : Prop :=
  vector_annihilates_right A.transpose

def vector_annihilates : Prop :=
  vector_annihilates_right A ∨ vector_annihilates_left A

lemma vector_annihilates_det_eq_zero_iff :
  vector_annihilates A ↔ A.det = 0 :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    { rcases h with ⟨μ, hμ, h⟩,
      by_contradiction h₁,
      have h₂ := det_ne_zero_invertible A h₁,
      let AA : invertible_matrix n := ⟨A, h₂⟩,
      have h₃ := calc μ = 1 • μ
          : by rw one_smul
        ... = (AA⁻¹ * AA).val • μ
          : by rw mul_left_inv; simp
        ... = ((AA⁻¹).val * A) • μ
          : by simp
        ... = (AA⁻¹).val • (A • μ)
          : by rw mul_smul
        ... = 0
          : by rw [h, smul_zero],
      exact hμ h₃ },
    { rcases h with ⟨μ, hμ, h⟩,
      by_contradiction h₁,
      have h₁ : A.transpose.det ≠ 0 := by rw transpose_det; exact h₁,
      have h₂ := det_ne_zero_invertible A.transpose h₁,
      let AA : invertible_matrix n := ⟨A.transpose, h₂⟩,
      have h₃ := calc μ = 1 • μ
          : by rw one_smul
        ... = (AA⁻¹ * AA).val • μ
          : by rw mul_left_inv; simp
        ... = ((AA⁻¹).val * A.transpose) • μ
          : by simp
        ... = (AA⁻¹).val • (A.transpose • μ)
          : by rw mul_smul
        ... = 0
          : by rw [h, smul_zero],
      exact hμ h₃ }},
  { intro h,
    sorry }
end

/- `A` is either annihilated by a vector on the left or on the right,
  otherwise it muse be an invertible matrix  -/
lemma vector_annihilates_or_ivertible :
  vector_annihilates A ∨ is_invertible A :=
begin
  rw vector_annihilates_det_eq_zero_iff,
  rw ←det_ne_zero_iff,
  apply classical.em
end

end miscs

end FG
