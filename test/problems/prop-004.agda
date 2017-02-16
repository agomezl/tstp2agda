
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
goal = ((¬ y ⇒ ¬ x) ⇒ ((¬ y ⇒ x) ⇒ y))


-- Subgoal
subgoal₀ : Prop
subgoal₀ = (((¬ y ⇒ ¬ x) ∧ (¬ y ⇒ x)) ⇒ y)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-conjunct $  -- Γ ⊢ (x ∨ y)
            atp-canonicalize $  -- Γ ⊢ ((¬ y ∧ (¬ x ∨ y)) ∧ (x ∨ y))
              atp-strip $  -- Γ ⊢ (((¬ y ⇒ ¬ x) ∧ (¬ y ⇒ x)) ⇒ y)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((¬ y ⇒ ¬ x) ∧ (¬ y ⇒ x)) ⇒ y)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-simplify $  -- Γ ⊢ ¬ x
              ∧-intro
                (
                atp-conjunct $  -- Γ ⊢ (¬ x ∨ y)
                  atp-canonicalize $  -- Γ ⊢ ((¬ y ∧ (¬ x ∨ y)) ∧ (x ∨ y))
                    atp-strip $  -- Γ ⊢ (((¬ y ⇒ ¬ x) ∧ (¬ y ⇒ x)) ⇒ y)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ (((¬ y ⇒ ¬ x) ∧ (¬ y ⇒ x)) ⇒ y)
                        atp-neg subgoal₀
                )
                (
                atp-conjunct $  -- Γ ⊢ ¬ y
                  atp-canonicalize $  -- Γ ⊢ ((¬ y ∧ (¬ x ∨ y)) ∧ (x ∨ y))
                    atp-strip $  -- Γ ⊢ (((¬ y ⇒ ¬ x) ∧ (¬ y ⇒ x)) ⇒ y)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ (((¬ y ⇒ ¬ x) ∧ (¬ y ⇒ x)) ⇒ y)
                        atp-neg subgoal₀
                )
            )
            (
            atp-conjunct $  -- Γ ⊢ ¬ y
              atp-canonicalize $  -- Γ ⊢ ((¬ y ∧ (¬ x ∨ y)) ∧ (x ∨ y))
                atp-strip $  -- Γ ⊢ (((¬ y ⇒ ¬ x) ∧ (¬ y ⇒ x)) ⇒ y)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((¬ y ⇒ ¬ x) ∧ (¬ y ⇒ x)) ⇒ y)
                    atp-neg subgoal₀
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

