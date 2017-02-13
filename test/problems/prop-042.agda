
-- tstp2agda proof

open import Data.FOL.Deep 2
open import Data.FOL.Deep.ATP.Metis 2

-- Vars
x : Prop
x = Var (# 0)

y : Prop
y = Var (# 1)

-- Axioms
a₁ : Prop
a₁ = x

a₂ : Prop
a₂ = y

-- Premises
Γ : Ctxt
Γ = ∅ , a₁ , a₂

-- Conjecture
goal : Prop
goal = (x ∨ y)

-- Subgoal
subgoal₀ : Prop
subgoal₀ = (¬ x ⇒ y)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        atp-canonicalize $
          atp-strip $
            assume {Γ = Γ} $
              atp-neg subgoal₀        )
        (
        atp-canonicalize $
          weaken (atp-neg subgoal₀) (assume {Γ = ∅} a₁)
        )
        (
        atp-canonicalize $
          weaken (atp-neg subgoal₀) (assume {Γ = ∅} a₂)
        )



