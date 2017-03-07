
-- tstp2agda proof

open import Data.FOL.Deep 2 public
open import Data.FOL.Deep.ATP.Metis 2 public

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

-- Axiom
a₁ : Prop
a₁ = (p ∧ q)


-- Premise
Γ : Ctxt
Γ = [ a1 ]

-- Conjecture
goal : Prop
goal = (p ⇒ q)


-- Subgoal
subgoal₀ : Prop
subgoal₀ = (p ⇒ q)

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
          ∧-intro
            (
            ∧-proj₂ $ -- (q ≟ q)
              atp-canonicalize $  -- Γ ⊢ (p ∧ q)
                weaken (atp-neg subgoal₀) $
                  (assume {Γ = ∅} a1)
            )
            (
            ∧-proj₁ $ -- 3: p
              atp-canonicalize $  -- Γ ⊢ (p ∧ q)
                weaken (atp-neg subgoal₀) $
                  (assume {Γ = ∅} a1)
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

