
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
a₁ = (((p ∧ q) ⇒ q) ⇒ (q ⇒ p))


-- Premise
Γ : Ctxt
Γ = [ a1 ]

-- Conjecture
goal : Prop
goal = (q ⇒ p)


-- Subgoal
subgoal₀ : Prop
subgoal₀ = (q ⇒ p)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ (¬ p ∧ q)
            atp-strip $  -- Γ ⊢ (q ⇒ p)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ (q ⇒ p)
                atp-neg subgoal₀
          )
          (
          atp-canonicalize $  -- Γ ⊢ (¬ q ∨ p)
            weaken (atp-neg subgoal₀) $
              (assume {Γ = ∅} a1)
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

