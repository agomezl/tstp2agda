
-- tstp2agda proof

open import Data.FOL.Deep 3
open import Data.FOL.Deep.ATP.Metis 3

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

r : Prop
r = Var (# 2)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = ((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ⇒ (p ⇔ q))

-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ p) ⇒ q)

subgoal₁ : Prop
subgoal₁ = (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ q) ⇒ p)

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


