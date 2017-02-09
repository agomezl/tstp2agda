
-- tstp2agda proof

open import Data.FOL.Deep 2

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

-- Premise
Γ : Ctxt
Γ = ∅

-- Subgoal
subgoal-0 : Prop
subgoal-0 = (((p ⇒ q) ⇒ p) ⇒ p)

-- Conjecture
goal : Prop
goal = (((p ⇒ q) ⇒ p) ⇒ p)

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet
