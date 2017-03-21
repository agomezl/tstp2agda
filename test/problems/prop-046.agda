
-- tstp2agda proof

open import Data.FOL.Deep 2 public
open import Data.FOL.Deep.ATP.Metis 2 public

-- Vars
p1 : Prop
p1 = Var (# 0)

p2 : Prop
p2 = Var (# 1)

-- Axiom
axiom₁ : Prop
axiom₁ = (p1 ∧ p2)


-- Premise
Γ : Ctxt
Γ = [ axiom1 ]

-- Conjecture
goal : Prop
goal = p2


-- Subgoal
subgoal₀ : Prop
subgoal₀ = p2

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ¬ p2
            atp-strip $  -- Γ ⊢ p2
              assume {Γ = Γ} $  -- Γ ⊢ ¬ p2
                atp-neg subgoal₀
          )
          (
          ∧-proj₂ $ -- (p2 ≟ p2)
            atp-canonicalize $  -- Γ ⊢ (p1 ∧ p2)
              weaken (atp-neg subgoal₀) $
                (assume {Γ = ∅} axiom1)
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

