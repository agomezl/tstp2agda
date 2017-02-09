
-- tstp2agda proof

open import Data.FOL.Deep 4

-- Vars
a : Prop
a = Var (# 0)

g : Prop
g = Var (# 1)

k : Prop
k = Var (# 2)

q : Prop
q = Var (# 3)

-- Premise
Γ : Ctxt
Γ = ∅

-- Subgoal
subgoal-0 : Prop
subgoal-0 = (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)

-- Conjecture
goal : Prop
goal = (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet
