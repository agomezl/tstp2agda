
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
a₁ = (p ⇒ (q ⇒ r))


-- Premise
Γ : Ctxt
Γ = [ a1 ]

-- Conjecture
goal : Prop
goal = (q ⇒ (p ⇒ r))


-- Subgoal
subgoal₀ : Prop
subgoal₀ = ((q ∧ p) ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p) ∧ q)
            atp-strip $  -- Γ ⊢ ((q ∧ p) ⇒ r)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ ((q ∧ p) ⇒ r)
                atp-neg subgoal₀
          )
          (
          atp-canonicalize $  -- Γ ⊢ ((¬ p ∨ ¬ q) ∨ r)
            weaken (atp-neg subgoal₀) $
              (assume {Γ = ∅} a1)
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

