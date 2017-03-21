
-- tstp2agda proof

open import Data.FOL.Deep 2 public
open import Data.FOL.Deep.ATP.Metis 2 public

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

-- Axiom
axiom : Prop
axiom = (p ∧ q)


-- Premise
Γ : Ctxt
Γ = [ axiom ]

-- Conjecture
goal : Prop
goal = (q ∧ p)


-- Subgoals
subgoal₀ : Prop
subgoal₀ = q


subgoal₁ : Prop
subgoal₁ = (q ⇒ p)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ¬ q
            atp-strip $  -- Γ ⊢ q
              assume {Γ = Γ} $  -- Γ ⊢ ¬ q
                atp-neg subgoal₀
          )
          (
          ∧-proj₂ $ -- (q ≟ q)
            atp-canonicalize $  -- Γ ⊢ (p ∧ q)
              weaken (atp-neg subgoal₀) $
                (assume {Γ = ∅} axiom)
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ (¬ p ∧ q)
            atp-strip $  -- Γ ⊢ (q ⇒ p)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ (q ⇒ p)
                atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 3: p
              atp-canonicalize $  -- Γ ⊢ (p ∧ q)
                weaken (atp-neg subgoal₁) $
                  (assume {Γ = ∅} axiom)
            )
            (
            ∧-proj₂ $ -- (q ≟ q)
              atp-canonicalize $  -- Γ ⊢ (p ∧ q)
                weaken (atp-neg subgoal₁) $
                  (assume {Γ = ∅} axiom)
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

