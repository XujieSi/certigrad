import Lake

open Lake DSL

package certigrad

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.11.0-rc1"


@[default_target]
lean_lib CertiGrad
