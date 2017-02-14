
-- tstp2agda proof

open import Data.FOL.Deep 1 public
open import Data.FOL.Deep.ATP.Metis 1 public

-- Vars
p : Prop
p = Var (# 0)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = (p ∨ ¬ ¬ ¬ p)

-- Subgoal
subgoal₀ : Prop
subgoal₀ = (¬ p ⇒ ¬ p)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
 RAA $
    atp-canonicalize $
      atp-canonicalize $
        atp-strip $
          assume {Γ = Γ} $
            atp-neg subgoal₀

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀
