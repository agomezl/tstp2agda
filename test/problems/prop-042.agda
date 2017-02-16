
-- tstp2agda proof

open import Data.FOL.Deep 2 public
open import Data.FOL.Deep.ATP.Metis 2 public

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
Γ = ∅ , a1 , a2

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
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ (¬ x ∧ ¬ y)
            atp-strip $  -- Γ ⊢ (¬ x ⇒ y)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ (¬ x ⇒ y)
                atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-canonicalize $  -- Γ ⊢ x
              weaken (atp-neg subgoal₀) $
                (assume {Γ = ∅} a1)
            )
            (
            atp-canonicalize $  -- Γ ⊢ y
              weaken (atp-neg subgoal₀) $
                (assume {Γ = ∅} a2)
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

