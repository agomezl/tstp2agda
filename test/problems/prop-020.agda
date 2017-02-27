
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
goal = ((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ⇒ (p ⇔ q))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ p) ⇒ q)


subgoal₁ : Prop
subgoal₁ = (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ q) ⇒ p)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₁ $ -- 1: (((¬ q ∧ p) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r))
            atp-canonicalize $  -- Γ ⊢ ((((¬ q ∧ p) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r)) ∧ (¬ r ∨ (p ∧ q)))
              atp-strip $  -- Γ ⊢ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ p) ⇒ q)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ p) ⇒ q)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (((¬ q ∧ p) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r))
              atp-canonicalize $  -- Γ ⊢ ((((¬ q ∧ p) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r)) ∧ (¬ r ∨ (p ∧ q)))
                atp-strip $  -- Γ ⊢ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ p) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ p) ⇒ q)
                    atp-neg subgoal₀
            )
            (
            ∧-proj₁ $ -- 1: (((¬ q ∧ p) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r))
              atp-canonicalize $  -- Γ ⊢ ((((¬ q ∧ p) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r)) ∧ (¬ r ∨ (p ∧ q)))
                atp-strip $  -- Γ ⊢ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ p) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ p) ⇒ q)
                    atp-neg subgoal₀
            )
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((¬ r ∨ (p ∧ q)) ≟ (¬ r ∨ (p ∧ q)))
            atp-canonicalize $  -- Γ ⊢ ((((¬ p ∧ q) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r)) ∧ (¬ r ∨ (p ∧ q)))
              atp-strip $  -- Γ ⊢ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ q) ⇒ p)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ q) ⇒ p)
                  atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            atp-simplify $  -- Γ ⊢ r
              ∧-intro
                (
                ∧-proj₁ $ -- 1: (((¬ p ∧ q) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r))
                  atp-canonicalize $  -- Γ ⊢ ((((¬ p ∧ q) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r)) ∧ (¬ r ∨ (p ∧ q)))
                    atp-strip $  -- Γ ⊢ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ q) ⇒ p)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ q) ⇒ p)
                        atp-neg subgoal₁
                )
                (
                ∧-proj₁ $ -- 1: (((¬ p ∧ q) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r))
                  atp-canonicalize $  -- Γ ⊢ ((((¬ p ∧ q) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r)) ∧ (¬ r ∨ (p ∧ q)))
                    atp-strip $  -- Γ ⊢ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ q) ⇒ p)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ q) ⇒ p)
                        atp-neg subgoal₁
                )
            )
            (
            ∧-intro
              (
              ∧-proj₁ $ -- 1: (((¬ p ∧ q) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r))
                atp-canonicalize $  -- Γ ⊢ ((((¬ p ∧ q) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r)) ∧ (¬ r ∨ (p ∧ q)))
                  atp-strip $  -- Γ ⊢ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ q) ⇒ p)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ q) ⇒ p)
                      atp-neg subgoal₁
              )
              (
              ∧-proj₁ $ -- 1: (((¬ p ∧ q) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r))
                atp-canonicalize $  -- Γ ⊢ ((((¬ p ∧ q) ∧ (¬ p ∨ (q ∧ r))) ∧ (¬ q ∨ r)) ∧ (¬ r ∨ (p ∧ q)))
                  atp-strip $  -- Γ ⊢ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ q) ⇒ p)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((q ⇒ r) ∧ (r ⇒ (p ∧ q))) ∧ (p ⇒ (q ∧ r))) ∧ q) ⇒ p)
                      atp-neg subgoal₁
              )
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

