
-- tstp2agda proof

open import Data.FOL.Deep 3 public
open import Data.FOL.Deep.ATP.Metis 3 public

-- Vars
x : Prop
x = Var (# 0)

y : Prop
y = Var (# 1)

z : Prop
z = Var (# 2)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = ((x ⇒ y) ⇒ (¬ (y ∨ z) ⇒ ¬ (x ∨ z)))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((x ⇒ y) ∧ ¬ (y ∨ z)) ⇒ ¬ x)


subgoal₁ : Prop
subgoal₁ = ((((x ⇒ y) ∧ ¬ (y ∨ z)) ∧ ¬ x) ⇒ ¬ z)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-conjunct $  -- Γ ⊢ (¬ x ∨ y)
            atp-canonicalize $  -- Γ ⊢ (((¬ y ∧ ¬ z) ∧ x) ∧ (¬ x ∨ y))
              atp-strip $  -- Γ ⊢ (((x ⇒ y) ∧ ¬ (y ∨ z)) ⇒ ¬ x)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((x ⇒ y) ∧ ¬ (y ∨ z)) ⇒ ¬ x)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-conjunct $  -- Γ ⊢ x
              atp-canonicalize $  -- Γ ⊢ (((¬ y ∧ ¬ z) ∧ x) ∧ (¬ x ∨ y))
                atp-strip $  -- Γ ⊢ (((x ⇒ y) ∧ ¬ (y ∨ z)) ⇒ ¬ x)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((x ⇒ y) ∧ ¬ (y ∨ z)) ⇒ ¬ x)
                    atp-neg subgoal₀
            )
            (
            atp-conjunct $  -- Γ ⊢ ¬ y
              atp-canonicalize $  -- Γ ⊢ (((¬ y ∧ ¬ z) ∧ x) ∧ (¬ x ∨ y))
                atp-strip $  -- Γ ⊢ (((x ⇒ y) ∧ ¬ (y ∨ z)) ⇒ ¬ x)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((x ⇒ y) ∧ ¬ (y ∨ z)) ⇒ ¬ x)
                    atp-neg subgoal₀
            )
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-canonicalize $  -- Γ ⊢ ⊥
        atp-strip $  -- Γ ⊢ ((((x ⇒ y) ∧ ¬ (y ∨ z)) ∧ ¬ x) ⇒ ¬ z)
          assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((x ⇒ y) ∧ ¬ (y ∨ z)) ∧ ¬ x) ⇒ ¬ z)
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

