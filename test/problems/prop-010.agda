
-- tstp2agda proof

open import Data.FOL.Deep 4
open import Data.FOL.Deep.ATP.Metis 4

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

-- Conjecture
goal : Prop
goal = (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)

-- Subgoal
subgoal₀ : Prop
subgoal₀ = (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet


