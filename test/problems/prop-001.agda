
-- tstp2agda proof

open import Data.FOL.Deep 1

-- Vars
a : Prop
a = Var (# 0)

-- Axiom
lm : Prop
lm = a

-- Premise
Γ : Ctxt
Γ = [ lm ]


-- Subgoal
subgoal-0 : Prop
subgoal-0 = a

-- Conjecture
goal : Prop
goal = a

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet
