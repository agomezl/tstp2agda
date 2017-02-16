
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
  -- Γ , ¬ subgoal₀⊢ ⊥
    atp-canonicalize $
      atp-simplify $
        ∧-intro
          (
          atp-conjunct $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
                    atp-neg subgoal₀
            )
            (
            atp-simplify $
              ∧-intro
                (
                atp-conjunct $
                  atp-canonicalize $
                    atp-strip $
                      assume {Γ = Γ} $
                        atp-neg subgoal₀
                )
                (
                atp-conjunct $
                  atp-canonicalize $
                    atp-strip $
                      assume {Γ = Γ} $
                        atp-neg subgoal₀
                )
            )
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
  -- Γ , ¬ subgoal₁⊢ ⊥
    atp-canonicalize $
      atp-simplify $
        ∧-intro
          (
          atp-conjunct $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
                    atp-neg subgoal₁
            )
            (
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
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

