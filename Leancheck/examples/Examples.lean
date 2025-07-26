import Leancheck
import Std

open Std

/--
info: Ok, passed 100 tests. 0 tests have timed out
-/
#guard_msgs in #eval leanCheck (λ x => x + 1 = x + 1)
