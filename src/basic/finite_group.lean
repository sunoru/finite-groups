import ..fglib

namespace FG

section finite_group

variable (α : Type)

/- ## Finite Group

  A `finite_group` is a `group` with a finite set of elements (`fintype`).
 -/
class finite_group extends group α, fintype α

end finite_group

end FG
