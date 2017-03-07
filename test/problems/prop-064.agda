
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

-- Axiom
a₁ : Prop
a₁ = ((p ⇒ q) ∧ (p ⇒ r))


-- Premise
Γ : Ctxt
Γ = [ a1 ]

-- Conjecture
goal : Prop
goal = (p ⇒ (q ∧ r))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (p ⇒ q)


subgoal₁ : Prop
subgoal₁ = ((p ∧ q) ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ (¬ q ∧ p)
            atp-strip $  -- Γ ⊢ (p ⇒ q)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ q)
                atp-neg subgoal₀
          )
          (
          ∧-proj₁ $ -- 1: (¬ p ∨ q)
            atp-canonicalize $  -- Γ ⊢ ((¬ p ∨ q) ∧ (¬ p ∨ r))
              weaken (atp-neg subgoal₀) $
                (assume {Γ = ∅} a1)
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p) ∧ q)
            atp-strip $  -- Γ ⊢ ((p ∧ q) ⇒ r)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ ((p ∧ q) ⇒ r)
                atp-neg subgoal₁
          )
          (
          ∧-proj₂ $ -- ((¬ p ∨ r) ≟ (¬ p ∨ r))
            atp-canonicalize $  -- Γ ⊢ ((¬ p ∨ q) ∧ (¬ p ∨ r))
              weaken (atp-neg subgoal₁) $
                (assume {Γ = ∅} a1)
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

