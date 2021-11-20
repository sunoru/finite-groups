import ..fglib
import ..bases.finite_group

namespace FG

namespace example_Z₃

inductive Z₃ : Type
| e : Z₃
| a : Z₃
| b : Z₃

namespace Z₃

def mul : Z₃ → Z₃ → Z₃
| Z₃.e y    := y
| x    Z₃.e := x
| Z₃.a Z₃.a := Z₃.b
| Z₃.a Z₃.b := Z₃.e
| Z₃.b Z₃.a := Z₃.e
| Z₃.b Z₃.b := Z₃.a

def inv : Z₃ → Z₃
| Z₃.e := Z₃.e
| Z₃.a := Z₃.b
| Z₃.b := Z₃.a

instance Z₃ : finite_group Z₃ :=
sorry

end Z₃

end example_Z₃

end FG
