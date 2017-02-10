
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
goal = ((p ⇔ q) ⇔ ((q ∨ ¬ p) ∧ (¬ q ∨ p)))

-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((p ⇔ q) ∧ ¬ q) ⇒ ¬ p)

subgoal₁ : Prop
subgoal₁ = ((((p ⇔ q) ∧ (q ∨ ¬ p)) ∧ ¬ ¬ q) ⇒ p)

subgoal₂ : Prop
subgoal₂ = ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ p) ⇒ q)

subgoal₃ : Prop
subgoal₃ = ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ q) ⇒ p)

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


