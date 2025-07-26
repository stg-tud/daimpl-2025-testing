import Leancheck
import Std

open Std

#guard_msgs(error) in #eval leanCheck (λ x => x + 1 = x + 1)
