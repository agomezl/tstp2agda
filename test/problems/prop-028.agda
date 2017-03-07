
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
          ∧-proj₂ $ -- ((p ∨ q) ≟ (p ∨ q))
            atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
              atp-strip $  -- Γ ⊢ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: ((¬ p ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p))
              atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
                atp-strip $  -- Γ ⊢ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                    atp-neg subgoal₀
            )
            (
            atp-simplify $  -- Γ ⊢ ¬ q
              ∧-intro
                (
                ∧-proj₁ $ -- 1: ((¬ p ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p))
                  atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
                    atp-strip $  -- Γ ⊢ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)
                        atp-neg subgoal₀
                )
                (
                ∧-proj₁ $ -- 1: ((¬ p ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p))
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
          ∧-proj₁ $ -- 1: (((¬ r ∧ p) ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p))
            atp-canonicalize $  -- Γ ⊢ ((((¬ r ∧ p) ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
              atp-strip $  -- Γ ⊢ (((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ∧ p) ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ∧ p) ⇒ r)
                  atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (((¬ r ∧ p) ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p))
              atp-canonicalize $  -- Γ ⊢ ((((¬ r ∧ p) ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
                atp-strip $  -- Γ ⊢ (((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ∧ p) ⇒ r)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ∧ p) ⇒ r)
                    atp-neg subgoal₁
            )
            (
            ∧-proj₁ $ -- 1: (((¬ r ∧ p) ∧ (¬ p ∨ r)) ∧ (¬ q ∨ p))
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

