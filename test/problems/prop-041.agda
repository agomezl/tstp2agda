
-- tstp2agda proof

open import Data.FOL.Deep 1
open import Data.FOL.Deep.ATP.Metis 1

-- Vars
$true : Prop
$true = ⊤

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = ¬ $false

-- Subgoal
subgoal₀ : Prop
subgoal₀ = $true

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $
      atp-canonicalize $
        atp-strip $
          assume {Γ = Γ} $
            atp-neg subgoal₀


