
-- tstp2agda proof

open import Data.FOL.Deep 4
open import Data.FOL.Deep.ATP.Metis 4

-- Vars
a : Prop
a = Var (# 0)

b : Prop
b = Var (# 1)

c : Prop
c = Var (# 2)

d : Prop
d = Var (# 3)

-- Axioms
a₁ : Prop
a₁ = a

a₂ : Prop
a₂ = b

a₃ : Prop
a₃ = ((¬ a ∨ ¬ b) ∨ c)

a₄ : Prop
a₄ = (¬ c ∨ d)

-- Premises
Γ : Ctxt
Γ = ∅ , a1 , a2 , a3 , a4

-- Conjecture
a₅ : Prop
a₅ = ((d ∧ a) ∨ (b ∧ c))

-- Subgoals
subgoal₀ : Prop
subgoal₀ = (¬ (d ∧ a) ⇒ b)

subgoal₁ : Prop
subgoal₁ = ((¬ (d ∧ a) ∧ b) ⇒ c)

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


