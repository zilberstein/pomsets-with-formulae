import Pom.Order.FinApprox

instance {l : Type} [DCPO l] [ScottCompact l] [OrderBot l] : ChainCompletePartialOrder (Pom l) where
  cSup := sorry
  le_cSup := sorry
  cSup_le := sorry
