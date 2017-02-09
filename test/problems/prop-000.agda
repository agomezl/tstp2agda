
-- tstp2agda proof

open import Data.FOL.Deep 1
open import Data.FOL.Deep.ATP.Metis 1
-- Vars
$true : Prop
$true = Var (# 0)

-- Premise
Γ : Ctxt
Γ = ∅

-- Subgoal
subgoal-0 : Prop
subgoal-0 = $true

-- Conjecture
goal : Prop
goal = $true

-- Proof
proof : Γ ⊢ goal
proof =
  RAA $
    atp-canonicalize $
      atp-canonicalize $
        (atp-canonicalize $
          (assume {Γ = Γ} (atp-neg (atp-strip {!!}))))

