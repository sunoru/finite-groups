import ..fglib

namespace FG

section finite_group

variable (α : Type)

class finite_group extends group α, fintype α

end finite_group

end FG
