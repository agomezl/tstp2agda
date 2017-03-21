
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
goal = (p ⇒ ((p ⇒ q) ⇒ q))


-- Subgoal
subgoal₀ : Prop
subgoal₀ = ((p ∧ (p ⇒ q)) ⇒ q)

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
              atp-strip $  -- Γ ⊢ ((p ∧ (p ⇒ q)) ⇒ q)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((p ∧ (p ⇒ q)) ⇒ q)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (¬ q ∧ p)
              atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ p) ∧ (¬ p ∨ q))
                atp-strip $  -- Γ ⊢ ((p ∧ (p ⇒ q)) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((p ∧ (p ⇒ q)) ⇒ q)
                    atp-neg subgoal₀
            )
            (
            ∧-proj₁ $ -- 1: (¬ q ∧ p)
              atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ p) ∧ (¬ p ∨ q))
                atp-strip $  -- Γ ⊢ ((p ∧ (p ⇒ q)) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((p ∧ (p ⇒ q)) ⇒ q)
                    atp-neg subgoal₀
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

