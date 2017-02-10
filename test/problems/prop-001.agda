
-- tstp2agda proof

open import Data.FOL.Deep 1
open import Data.FOL.Deep.ATP.Metis 1

-- Vars
a : Prop
a = Var (# 0)

-- Axiom
lm : Prop
lm = a

-- Premise
Γ : Ctxt
Γ = [ lm ]


-- Conjecture
goal : Prop
goal = a

-- Subgoal
subgoal₀ : Prop
subgoal₀ = a

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet


