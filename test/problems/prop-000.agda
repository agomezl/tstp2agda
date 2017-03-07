
-- tstp2agda proof

open import Data.FOL.Deep 1 public
open import Data.FOL.Deep.ATP.Metis 1 public

-- Vars
$true : Prop
$true = ⊤

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = $true


-- Subgoal
subgoal₀ : Prop
subgoal₀ = $true

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-canonicalize $  -- Γ ⊢ ⊥
        atp-strip $  -- Γ ⊢ $true
          assume {Γ = Γ} $  -- Γ ⊢ ¬ $true
            atp-neg subgoal₀

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

