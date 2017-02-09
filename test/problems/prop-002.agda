
-- tstp2agda proof

open import Data.FOL.Deep 2

-- Vars
x : Prop
x = Var (# 0)

y : Prop
y = Var (# 1)

-- Premise
Γ : Ctxt
Γ = ∅

-- Subgoal
subgoal-0 : Prop
subgoal-0 = ((x ∧ y) ⇒ x)

-- Conjecture
goal : Prop
goal = (x ⇒ (y ⇒ x))

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
    atp-canonicalize $
      atp-canonicalize $
        assume {Γ = Γ} $ atp-neg $
          atp-strip $
            goal

