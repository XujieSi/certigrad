import Lake

open Lake DSL

package certigrad

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.19.0"


@[default_target]
lean_lib CertiGrad
