import ..fglib

namespace FG

/- General lemmas for vectors -/
section linear_space3

variables (α : Type) [field α]

structure vec3 :=
(x : α)
(y : α)
(z : α)

structure mat3 :=
(x : vec3 α)
(y : vec3 α)
(z : vec3 α)

end linear_space3

end FG
