import ..fglib
import ..basic

namespace FG

/- ## Vector

  Defined as a function from a finite natural number to the value on that dimension.
  Note that study complex numbers are studied here since
  they are the most commonly used field in physics. -/

def vec (n : ℕ) := (fin (n + 1) → ℂ)

namespace vec

variables {n : ℕ}

@[ext] theorem ext (v w : vec n) :
  (∀(i : fin (n + 1)), v i = w i) → v = w :=
funext

@[simp] def zero : vec n :=
  λ_, 0

@[simp] def map (f : ℂ → ℂ) (v : vec n) : vec n :=
  λi, f (v i)

@[simp] def map₂ (f : ℂ → ℂ → ℂ) (v w : vec n) : vec n :=
  λi, f (v i) (w i)

@[simp] def add (v w : vec n) : vec n :=
  map₂ (+) v w

@[simp] lemma mapped₂_nth (f : ℂ → ℂ → ℂ) (v w : vec n) :
  ∀(i : fin (n + 1)), (map₂ f v w) i = f (v i) (w i) :=
by intro i; simp

/- We can then show that `vec n` is an `add_comm_monoid`. -/
@[simps] instance : add_comm_monoid (vec n) :=
{ zero := zero,
  add := add,
  add_assoc :=
  begin
    intros a b c,
    apply ext,
    intro i,
    calc (a.add b).add c i = a.add b i + c i
        : by apply mapped₂_nth
      ... = a i + b i + c i
        : by rw add; rw mapped₂_nth (+) a b
      ... = a i + b.add c i
        : by rw [add, mapped₂_nth (+) b c, add_assoc]
      ... = (a.add (b.add c)) i
        : (mapped₂_nth (+) a (b.add c) i).symm
  end,
  zero_add :=
  begin
    intro a,
    apply ext,
    intro i,
    simp,
  end,
  add_zero :=
  begin
    intro a,
    apply ext,
    intro i,
    simp,
  end,
  add_comm :=
  begin
    intros a b,
    apply ext,
    intro i,
    calc a.add b i = a i + b i
        : by apply mapped₂_nth
      ... = b i + a i
        : by rw add_comm
      ... = b.add a i
        : by rw [add, mapped₂_nth (+) b a]
  end }

def smul (c : ℂ) (v : vec n) : vec n :=
  map (λx, c * x) v

/- and a module over `ℂ`. -/
@[simps] instance : module ℂ (vec n) :=
{ smul := smul,
  smul_zero :=
  begin
    intro a,
    apply ext,
    simp [smul]
  end,
  smul_add :=
  begin
    intros a v w,
    apply ext,
    intro i,
    simp [smul],
    ring
  end,
  zero_smul :=
  begin
    intro v,
    apply ext,
    simp [smul]
  end,
  one_smul :=
  begin
    intro v,
    apply ext,
    simp [smul]
  end,
  add_smul :=
  begin
    intros a v w,
    apply ext,
    intro i,
    simp [smul],
    ring
  end,
  mul_smul :=
  begin
    intros a v w,
    apply ext,
    intro i,
    simp [smul],
    ring
  end }

end vec

end FG
