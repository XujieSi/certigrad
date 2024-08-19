/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

References.
-/
-- import .id .tensor .util
import CertiGrad.Id
import CertiGrad.Tensor
import CertiGrad.Util

namespace certigrad

@[reducible] def Reference := ID × S

-- instance : BEq Reference where
--   beq

instance : Hashable Reference where
  hash := fun _ => 0

namespace reference

-- TODO(dhs): (much) better hash function
def hash : Reference → Nat
  | ref => 0

end reference
end certigrad
