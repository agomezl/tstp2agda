
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
goal = ((p ⇔ q) ⇔ ((q ∨ ¬ p) ∧ (¬ q ∨ p)))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((p ⇔ q) ∧ ¬ q) ⇒ ¬ p)


subgoal₁ : Prop
subgoal₁ = ((((p ⇔ q) ∧ (q ∨ ¬ p)) ∧ ¬ ¬ q) ⇒ p)


subgoal₂ : Prop
subgoal₂ = ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ p) ⇒ q)


subgoal₃ : Prop
subgoal₃ = ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ q) ⇒ p)

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
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
                    atp-neg subgoal₀
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

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
  -- Γ , ¬ subgoal₂⊢ ⊥
    atp-canonicalize $
      atp-simplify $
        ∧-intro
          (
          atp-conjunct $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₂
          )
          (
          ∧-intro
            (
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
                    atp-neg subgoal₂
            )
            (
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
                    atp-neg subgoal₂
            )
          )

proof₃ : Γ ⊢ subgoal₃
proof₃ =
  RAA $
  -- Γ , ¬ subgoal₃⊢ ⊥
    atp-canonicalize $
      atp-simplify $
        ∧-intro
          (
          atp-conjunct $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₃
          )
          (
          ∧-intro
            (
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
                    atp-neg subgoal₃
            )
            (
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
                    atp-neg subgoal₃
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    (
    ∧-intro
      subgoal₀
      (
      ∧-intro
        subgoal₁
        (
        ∧-intro
          subgoal₂
          subgoal₃
        )
      )
    )

