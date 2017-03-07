
-- tstp2agda proof

open import Data.FOL.Deep 1 public
open import Data.FOL.Deep.ATP.Metis 1 public

-- Vars
a : Prop
a = Var (# 0)

-- Axiom
lm : Prop
lm = a


-- Premise
Γ : Ctxt
Γ = [ lm ]

-- Conjecture
goal : Prop
goal = a


-- Subgoal
subgoal₀ : Prop
subgoal₀ = a

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ¬ a
            atp-strip $  -- Γ ⊢ a
              assume {Γ = Γ} $  -- Γ ⊢ ¬ a
                atp-neg subgoal₀
          )
          (
          atp-canonicalize $  -- Γ ⊢ a
            weaken (atp-neg subgoal₀) $
              (assume {Γ = ∅} lm)
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

