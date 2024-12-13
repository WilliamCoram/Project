import Mathlib
-- infinite matrices are inherintly defined via usual matrix definition

-- We first will want to define generating functions

variable {R : Type*}



def GeneratingFunction : (Matrix m n R) → MvPowerSeries (x y) R  where
