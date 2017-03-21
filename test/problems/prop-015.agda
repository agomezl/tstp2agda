
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
goal = (((p ∨ q) ⇒ (p ∨ r)) ⇒ (p ∨ (q ⇒ r)))


-- Subgoal
subgoal₀ : Prop
subgoal₀ = (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- (((p ∨ r) ∨ (¬ p ∧ ¬ q)) ≟ ((p ∨ r) ∨ (¬ p ∧ ¬ q)))
            atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ r) ∧ q) ∧ ((p ∨ r) ∨ (¬ p ∧ ¬ q)))
              atp-strip $  -- Γ ⊢ (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: ((¬ p ∧ ¬ r) ∧ q)
              atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ r) ∧ q) ∧ ((p ∨ r) ∨ (¬ p ∧ ¬ q)))
                atp-strip $  -- Γ ⊢ (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                    atp-neg subgoal₀
            )
            (
            ∧-intro
              (
              ∧-proj₁ $ -- 1: ((¬ p ∧ ¬ r) ∧ q)
                atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ r) ∧ q) ∧ ((p ∨ r) ∨ (¬ p ∧ ¬ q)))
                  atp-strip $  -- Γ ⊢ (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                      atp-neg subgoal₀
              )
              (
              ∧-intro
                (
                ∧-proj₁ $ -- 1: ((¬ p ∧ ¬ r) ∧ q)
                  atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ r) ∧ q) ∧ ((p ∨ r) ∨ (¬ p ∧ ¬ q)))
                    atp-strip $  -- Γ ⊢ (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                        atp-neg subgoal₀
                )
                (
                ∧-proj₁ $ -- 1: ((¬ p ∧ ¬ r) ∧ q)
                  atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ r) ∧ q) ∧ ((p ∨ r) ∨ (¬ p ∧ ¬ q)))
                    atp-strip $  -- Γ ⊢ (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                        atp-neg subgoal₀
                )
              )
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

