import Lean.Meta.Tactic.Simp.RegisterCommand
open Lean Meta Simp

namespace CertiGrad
-- Simplification rules for CertiGrad gradients
  register_simp_attr grad_simp

  register_simp_attr cdiff_simp

  register_simp_attr precondition_simp
end CertiGrad
