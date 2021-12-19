import ..fglib

namespace FG

/- ## Finite Group

  A `finite_group` is a `group` with a finite set of elements (`fintype`). -/
class finite_group (α : Type) extends group α, fintype α

end FG
