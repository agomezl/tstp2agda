
-- tstp2agda proof

open import Data.FOL.Deep 2 public
open import Data.FOL.Deep.ATP.Metis 2 public

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
goal = (x ⇒ (y ⇒ x))


-- Subgoal
subgoal₀ : Prop
subgoal₀ = ((x ∧ y) ⇒ x)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-canonicalize $  -- Γ ⊢ ⊥
        atp-strip $  -- Γ ⊢ ((x ∧ y) ⇒ x)
          assume {Γ = Γ} $  -- Γ ⊢ ¬ ((x ∧ y) ⇒ x)
            atp-neg subgoal₀

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

