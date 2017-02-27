
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
goal = ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ ¬ (¬ q ∨ ¬ q))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ q)


subgoal₁ : Prop
subgoal₁ = (((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ∧ ¬ ¬ q) ⇒ q)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((p ∨ q) ≟ (p ∨ q))
            atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
              atp-strip $  -- Γ ⊢ ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ q)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ q)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-simplify $  -- Γ ⊢ ¬ p
              ∧-intro
                (
                ∧-proj₁ $ -- 1: ((¬ q ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p))
                  atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
                    atp-strip $  -- Γ ⊢ ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ q)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ q)
                        atp-neg subgoal₀
                )
                (
                ∧-proj₁ $ -- 1: ((¬ q ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p))
                  atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
                    atp-strip $  -- Γ ⊢ ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ q)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ q)
                        atp-neg subgoal₀
                )
            )
            (
            ∧-proj₁ $ -- 1: ((¬ q ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p))
              atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p)) ∧ (p ∨ q))
                atp-strip $  -- Γ ⊢ ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ q)
                    atp-neg subgoal₀
            )
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-canonicalize $  -- Γ ⊢ ⊥
        atp-strip $  -- Γ ⊢ (((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ∧ ¬ ¬ q) ⇒ q)
          assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ∧ ¬ ¬ q) ⇒ q)
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

