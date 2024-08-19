/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Random number generators.
-/

namespace certigrad
-- open list


axiom RNG : Type

namespace RNG

axiom mk : Nat → RNG
axiom to_string : RNG → String

-- instance : has_to_string RNG := has_to_string.mk to_string

end RNG
end certigrad
