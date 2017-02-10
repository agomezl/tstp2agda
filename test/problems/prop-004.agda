
-- tstp2agda proof

open import Data.FOL.Deep 2
open import Data.FOL.Deep.ATP.Metis 2

-- Vars
x : Prop
x = Var (# 0)

y : Prop
y = Var (# 1)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = ((¬ y ⇒ ¬ x) ⇒ ((¬ y ⇒ x) ⇒ y))

-- Subgoal
subgoal₀ : Prop
subgoal₀ = (((¬ y ⇒ ¬ x) ∧ (¬ y ⇒ x)) ⇒ y)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet


