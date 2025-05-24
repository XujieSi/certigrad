import Lean.Meta.Tactic.Simp.RegisterCommand
open Lean Meta Simp

namespace CertiGrad
-- Simplification rules for CertiGrad gradients
  register_simp_attr grad_simp

  -- Rules for proving CertiGrad.T.is_cdifferentiable
  register_simp_attr cdiff_simp

  -- Rules for proving preconditions (e.g., positivity) in CertiGrad
  register_simp_attr precondition_simp
end CertiGrad
