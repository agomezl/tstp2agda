
-- tstp2agda proof

open import Data.FOL.Deep 2 public
open import Data.FOL.Deep.ATP.Metis 2 public

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

-- Axioms
axiomp : Prop
axiomp = p


axiomq : Prop
axiomq = q


-- Premises
Γ : Ctxt
Γ = ∅ , axiomp , axiomq

-- Conjecture
goal : Prop
goal = (p ∧ q)


-- Subgoals
subgoal₀ : Prop
subgoal₀ = p


subgoal₁ : Prop
subgoal₁ = (p ⇒ q)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ¬ p
            atp-strip $  -- Γ ⊢ p
              assume {Γ = Γ} $  -- Γ ⊢ ¬ p
                atp-neg subgoal₀
          )
          (
          atp-canonicalize $  -- Γ ⊢ p
            weaken (atp-neg subgoal₀) $
              (assume {Γ = ∅} axiomp)
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ (¬ q ∧ p)
            atp-strip $  -- Γ ⊢ (p ⇒ q)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ q)
                atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            atp-canonicalize $  -- Γ ⊢ q
              weaken (atp-neg subgoal₁) $
                (assume {Γ = ∅} axiomq)
            )
            (
            atp-canonicalize $  -- Γ ⊢ p
              weaken (atp-neg subgoal₁) $
                (assume {Γ = ∅} axiomp)
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

