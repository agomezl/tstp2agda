
-- tstp2agda proof

open import Data.FOL.Deep 2
open import Data.FOL.Deep.ATP.Metis 2

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = ((p ⇒ q) ⇔ (¬ p ∨ q))

-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((p ⇒ q) ∧ ¬ ¬ p) ⇒ q)

subgoal₁ : Prop
subgoal₁ = (((¬ p ∨ q) ∧ p) ⇒ q)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet


proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet


