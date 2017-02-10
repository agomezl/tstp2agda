
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
goal = ((p ∨ (q ∧ r)) ⇔ ((p ∨ q) ∧ (p ∨ r)))

-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((p ∨ (q ∧ r)) ∧ ¬ p) ⇒ q)

subgoal₁ : Prop
subgoal₁ = ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)

subgoal₂ : Prop
subgoal₂ = ((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ⇒ q)

subgoal₃ : Prop
subgoal₃ = (((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)

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


proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet


proof₃ : Γ ⊢ subgoal₃
proof₃ =
  RAA $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet


