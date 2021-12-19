import ..fglib
import .representation

namespace FG

/- `ℂ` is a `module` on itself. The following is the `linear_operator` defined by complex multiplication. -/

@[simp] def complex.to_linear_operator (c : ℂ) :
  linear_operator ℂ ℂ :=
{ to_fun := λx, c * x,
  map_add' := λx y, by ring,
  map_smul' := λx r, by simp ; ring }

end FG
