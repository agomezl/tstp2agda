
-- tstp2agda proof

open import Data.FOL.Deep 1

-- Vars
p : Prop
p = Var (# 0)

-- Premise
Γ : Ctxt
Γ = ∅

-- Subgoal
subgoal-0 : Prop
subgoal-0 = (¬ p ⇒ ¬ p)

-- Conjecture
goal : Prop
goal = (p ∨ ¬ p)

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
    atp-canonicalize $
      atp-canonicalize $
        assume {Γ = Γ} $ atp-neg $
          atp-strip $
            goal

