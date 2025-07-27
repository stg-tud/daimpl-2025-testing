import Leancheck
import Std

open Std

-- Example for a successful unit test
#eval leanCheck (λ x => x + 1 = x + 1)

-- Example for a failing unit test
#eval leanCheck (λ x => x + 1 = x + 0)
