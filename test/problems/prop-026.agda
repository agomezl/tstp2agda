
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
goal = ((p ⇒ q) ∨ (q ⇒ p))


-- Subgoal
subgoal₀ : Prop
subgoal₀ = ((¬ (p ⇒ q) ∧ q) ⇒ p)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-canonicalize $  -- Γ ⊢ ⊥
        atp-strip $  -- Γ ⊢ ((¬ (p ⇒ q) ∧ q) ⇒ p)
          assume {Γ = Γ} $  -- Γ ⊢ ¬ ((¬ (p ⇒ q) ∧ q) ⇒ p)
            atp-neg subgoal₀

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

