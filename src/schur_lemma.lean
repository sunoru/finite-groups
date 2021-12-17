import .fglib
import .basic
import .linear_space
import .matrix_representation

namespace FG

/- ## Schur's lemma -/

open matrix_representation
open square_matrix
open invertible_matrix

namespace schur_lemma

variables {n : ℕ} (A : square_matrix n)

/- If `D₁` and `D₂` are inequivalent, irreducible representations,
  and `∀g ∈ G, D₁(g) * A = A * D₂(g)`, then `A = 0` -/

def vector_annihilates_right : Prop :=
  ∃(μ : vec n), μ ≠ 0 ∧ A.mul_vec μ = 0

def vector_annihilates_left : Prop :=
  ∃(ν : vec n), ν ≠ 0 ∧ A.transpose.mul_vec ν = 0

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

@[simp] def get_projector (v : vec n) : square_matrix n :=
  λi _, v i

@[simp] lemma has_project_annihilates (μ : vec n) (hμ : μ ≠ 0) (h : A.mul_vec μ = 0) :
  get_projector μ ≠ 0 ∧ A * get_projector μ = 0 :=
begin
  apply and.intro,
  { intro hp,
    apply hμ,
    funext i,
    simp *,
    rw ←matrix.ext_iff at hp,
    simp at hp,
    apply hp,
    exact i },
  { funext i j,
    simp [matrix.mul, *],
    have h₁ : (0 : square_matrix n) i j = 0 := rfl,
    rw h₁,
    unfold square_matrix.mul_vec at h,
    calc matrix.dot_product (A i) μ = (matrix.mul_vec A μ) i
        : by simp [matrix.mul_vec]
      ... = 0
        : by simp * }
end

lemma projection_annihilates_vanish {G : Type} [group G]
    (P  : square_matrix n)
    (D  : matrix_representation n G)
    (hD : is_irreducible D)
    (hp : P ≠ 0)
    (h  : ∀(g : G), A * (D.f g).val * P = 0) :
  A = 0 :=
begin
  /- TODO: An irreducible representation `D` is projected onto the whole space, so `A` must vanish. -/
  sorry
end

lemma schur_lemma₁ {G : Type} [group G] 
    (D₁ D₂ : matrix_representation n G)
    (h_inequivalent : ¬is_equivalent D₁ D₂)
    (h_irreducible₁ : is_irreducible D₁)
    (h_irreducible₂ : is_irreducible D₂)
    (h : ∀(g : G), (D₁.f g).val * A = A * (D₂.f g).val) :
  A = 0 :=
begin
  cases' classical.em (A = 0) with _ ha_ne_zero,
  { assumption },
  cases' classical.em (is_invertible A) with h₁ h₁,
  /- If `A` was invertible, `D₁` and `D₂` would be equivalent -/
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
  /- If `A` is not invertible, it must be `0` -/
  { cases' classical.em (vector_annihilates_right A) with h₂ h₂,
    { cases' h₂ with μ h₂,
      cases' h₂ with h₂ h₃,
      let P : square_matrix n := get_projector μ,
      have h₄ := has_project_annihilates A μ h₂ h₃,
      cases' h₄ with hp h₄,
      have h₅ := λ(g : G), calc A * (D₂.f g).val * P = (D₁.f g).val * A * P
          : by rw ←(h g)
        ... = (D₁.f g).val * 0
          : by rw [mul_assoc, h₄]
        ... = 0
          : mul_zero _,
      -- Since `D₂` is irreducible, `A` must be zero.
      apply projection_annihilates_vanish A P D₂ h_irreducible₂ hp h₅ },
    { -- When `vector_annihilates_left A`, it's similar to the case above.
      sorry }}
end

/-
  If `∀g ∈ G, D(g) * A = A * D(g)` and `D` is a finite dimensional
  irreducible representation, then `A ∝ I`.

  In other words, if a matrix commutes with all the elements of
  a finite dimensional irreducible representation,
  it is proportional to the identity.
-/

lemma schur_lemma₂ {G : Type} [finite_group G] 
    (D : matrix_representation n G)
    (h_irreducible : is_irreducible D)
    (h : ∀(g : G), (D.f g).val * A = A * (D.f g).val) :
  ∃(a : ℂ), A = a • square_matrix.I :=
begin
  /- Similar to a step above -/
  rcases A.has_nonzero_eigenvalue_and_eigenvector with ⟨γ, μ, hγ, hμ, h₁, h₂⟩,
  have h₃ := λ(g : G), calc (D.f g).val * (A - γ • I) = (D.f g).val * A - (D.f g).val * (γ • I)
      : mul_sub _ _ _
    ... = A * (D.f g).val - (D.f g).val * (γ • I)
      : by rw h g
    ... = A * (D.f g).val - γ • ((D.f g).val * I)
      : by simp
    ... = A * (D.f g).val - (γ • I) * (D.f g).val
      : by simp
    ... = (A - γ • I) * (D.f g).val
      : by rw sub_mul _ _ _,
  use γ,
  let P := get_projector μ,
  have h₄ := has_project_annihilates (A - γ • I) μ hμ h₂,
  cases' h₄ with hp h₄,
  -- have hp : get_projector μ = P := rfl,
  -- rw hp at h₄,
  have h₅ := λ(g : G), calc (A - γ • I) * (D.f g).val * P = (D.f g).val * ((A - γ • I) * P)
      : by rw [←h₃, mul_assoc]
    ... = (D.f g).val * 0
      : by rw h₄
    ... = 0
      : mul_zero _,
  have h₆ := projection_annihilates_vanish (A - γ • I) P D h_irreducible hp h₅,
  rw sub_eq_zero at h₆,
  exact h₆
end

end schur_lemma

end FG
