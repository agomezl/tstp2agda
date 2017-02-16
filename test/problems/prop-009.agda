
-- tstp2agda proof

open import Data.FOL.Deep 3 public
open import Data.FOL.Deep.ATP.Metis 3 public

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

r : Prop
r = Var (# 2)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ (p ∧ r))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)


subgoal₁ : Prop
subgoal₁ = (((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ∧ p) ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-conjunct $  -- Γ ⊢ (p ∨ q)
            atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
              atp-strip $  -- Γ ⊢ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-conjunct $  -- Γ ⊢ ¬ p
              atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
                atp-strip $  -- Γ ⊢ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                    atp-neg subgoal₀
            )
            (
            atp-simplify $  -- Γ ⊢ ¬ q
              ∧-intro
                (
                atp-conjunct $  -- Γ ⊢ (¬ q ∨ p)
                  atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
                    atp-strip $  -- Γ ⊢ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                        atp-neg subgoal₀
                )
                (
                atp-conjunct $  -- Γ ⊢ ¬ p
                  atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
                    atp-strip $  -- Γ ⊢ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                        atp-neg subgoal₀
                )
            )
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-conjunct $  -- Γ ⊢ (¬ p ∨ r)
            atp-canonicalize $  -- Γ ⊢ ((((¬ r ∧ p) ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
              atp-strip $  -- Γ ⊢ (((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ∧ p) ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ∧ p) ⇒ r)
                  atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            atp-conjunct $  -- Γ ⊢ p
              atp-canonicalize $  -- Γ ⊢ ((((¬ r ∧ p) ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
                atp-strip $  -- Γ ⊢ (((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ∧ p) ⇒ r)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ∧ p) ⇒ r)
                    atp-neg subgoal₁
            )
            (
            atp-conjunct $  -- Γ ⊢ ¬ r
              atp-canonicalize $  -- Γ ⊢ ((((¬ r ∧ p) ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
                atp-strip $  -- Γ ⊢ (((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ∧ p) ⇒ r)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ∧ p) ⇒ r)
                    atp-neg subgoal₁
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    (
    ∧-intro
      subgoal₀
      subgoal₁
    )

