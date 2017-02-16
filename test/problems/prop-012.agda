
-- tstp2agda proof

open import Data.FOL.Deep 1 public
open import Data.FOL.Deep.ATP.Metis 1 public

-- Vars
p : Prop
p = Var (# 0)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = (¬ ¬ p ⇔ p)


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (¬ ¬ p ⇒ p)


subgoal₁ : Prop
subgoal₁ = (p ⇒ p)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-canonicalize $  -- Γ ⊢ ⊥
        atp-strip $  -- Γ ⊢ (¬ ¬ p ⇒ p)
          assume {Γ = Γ} $  -- Γ ⊢ ¬ (¬ ¬ p ⇒ p)
            atp-neg subgoal₀

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-canonicalize $  -- Γ ⊢ ⊥
        atp-strip $  -- Γ ⊢ (p ⇒ p)
          assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ p)
            atp-neg subgoal₁

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    (
    ∧-intro
      subgoal₀
      subgoal₁
    )

