
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
subgoal-0 = (((¬ y ⇒ ¬ x) ∧ (¬ y ⇒ x)) ⇒ y)

-- Conjecture
goal : Prop
goal = ((¬ y ⇒ ¬ x) ⇒ ((¬ y ⇒ x) ⇒ y))

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet
