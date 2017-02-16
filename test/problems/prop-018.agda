
-- tstp2agda proof

open import Data.FOL.Deep 2 public
open import Data.FOL.Deep.ATP.Metis 2 public

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
goal = (((p ⇒ q) ⇒ p) ⇒ p)


-- Subgoal
subgoal₀ : Prop
subgoal₀ = (((p ⇒ q) ⇒ p) ⇒ p)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-conjunct $  -- Γ ⊢ (p ∨ (¬ q ∧ p))
            atp-canonicalize $  -- Γ ⊢ (¬ p ∧ (p ∨ (¬ q ∧ p)))
              atp-strip $  -- Γ ⊢ (((p ⇒ q) ⇒ p) ⇒ p)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ⇒ q) ⇒ p) ⇒ p)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-conjunct $  -- Γ ⊢ ¬ p
              atp-canonicalize $  -- Γ ⊢ (¬ p ∧ (p ∨ (¬ q ∧ p)))
                atp-strip $  -- Γ ⊢ (((p ⇒ q) ⇒ p) ⇒ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ⇒ q) ⇒ p) ⇒ p)
                    atp-neg subgoal₀
            )
            (
            atp-conjunct $  -- Γ ⊢ ¬ p
              atp-canonicalize $  -- Γ ⊢ (¬ p ∧ (p ∨ (¬ q ∧ p)))
                atp-strip $  -- Γ ⊢ (((p ⇒ q) ⇒ p) ⇒ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ⇒ q) ⇒ p) ⇒ p)
                    atp-neg subgoal₀
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

