
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
a₁ = (p ∨ q)


-- Premise
Γ : Ctxt
Γ = [ a1 ]

-- Conjecture
goal : Prop
goal = ((p ∨ q) ∨ r)


-- Subgoal
subgoal₀ : Prop
subgoal₀ = ((¬ p ∧ ¬ q) ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ((¬ p ∧ ¬ q) ∧ ¬ r)
            atp-strip $  -- Γ ⊢ ((¬ p ∧ ¬ q) ⇒ r)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ ((¬ p ∧ ¬ q) ⇒ r)
                atp-neg subgoal₀
          )
          (
          atp-canonicalize $  -- Γ ⊢ (p ∨ q)
            weaken (atp-neg subgoal₀) $
              (assume {Γ = ∅} a1)
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

