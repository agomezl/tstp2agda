
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
goal = ((p ⇒ q) ⇔ (¬ q ⇒ ¬ p))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((p ⇒ q) ∧ ¬ q) ⇒ ¬ p)


subgoal₁ : Prop
subgoal₁ = (((¬ q ⇒ ¬ p) ∧ p) ⇒ q)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((¬ p ∨ q) ≟ (¬ p ∨ q))
            atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ p) ∧ (¬ p ∨ q))
              atp-strip $  -- Γ ⊢ (((p ⇒ q) ∧ ¬ q) ⇒ ¬ p)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ⇒ q) ∧ ¬ q) ⇒ ¬ p)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (¬ q ∧ p)
              atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ p) ∧ (¬ p ∨ q))
                atp-strip $  -- Γ ⊢ (((p ⇒ q) ∧ ¬ q) ⇒ ¬ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ⇒ q) ∧ ¬ q) ⇒ ¬ p)
                    atp-neg subgoal₀
            )
            (
            ∧-proj₁ $ -- 1: (¬ q ∧ p)
              atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ p) ∧ (¬ p ∨ q))
                atp-strip $  -- Γ ⊢ (((p ⇒ q) ∧ ¬ q) ⇒ ¬ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ⇒ q) ∧ ¬ q) ⇒ ¬ p)
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
          ∧-proj₂ $ -- ((¬ p ∨ q) ≟ (¬ p ∨ q))
            atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ p) ∧ (¬ p ∨ q))
              atp-strip $  -- Γ ⊢ (((¬ q ⇒ ¬ p) ∧ p) ⇒ q)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((¬ q ⇒ ¬ p) ∧ p) ⇒ q)
                  atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (¬ q ∧ p)
              atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ p) ∧ (¬ p ∨ q))
                atp-strip $  -- Γ ⊢ (((¬ q ⇒ ¬ p) ∧ p) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((¬ q ⇒ ¬ p) ∧ p) ⇒ q)
                    atp-neg subgoal₁
            )
            (
            ∧-proj₁ $ -- 1: (¬ q ∧ p)
              atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ p) ∧ (¬ p ∨ q))
                atp-strip $  -- Γ ⊢ (((¬ q ⇒ ¬ p) ∧ p) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((¬ q ⇒ ¬ p) ∧ p) ⇒ q)
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

