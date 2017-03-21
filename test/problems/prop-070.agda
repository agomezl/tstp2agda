
-- tstp2agda proof

open import Data.FOL.Deep 4 public
open import Data.FOL.Deep.ATP.Metis 4 public

-- Vars
p : Prop
p = Var (# 0)

p1 : Prop
p1 = Var (# 1)

q : Prop
q = Var (# 2)

r : Prop
r = Var (# 3)

-- Axiom
a₁ : Prop
a₁ = (((p ∨ q) ∨ r) ∨ p1)


-- Premise
Γ : Ctxt
Γ = [ a1 ]

-- Conjecture
goal : Prop
goal = (((p ∨ p1) ∨ r) ∨ q)


-- Subgoal
subgoal₀ : Prop
subgoal₀ = ((¬ (p ∨ p1) ∧ ¬ r) ⇒ q)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ p1) ∧ ¬ q) ∧ ¬ r)
            atp-strip $  -- Γ ⊢ ((¬ (p ∨ p1) ∧ ¬ r) ⇒ q)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ ((¬ (p ∨ p1) ∧ ¬ r) ⇒ q)
                atp-neg subgoal₀
          )
          (
          atp-canonicalize $  -- Γ ⊢ (((p ∨ p1) ∨ q) ∨ r)
            weaken (atp-neg subgoal₀) $
              (assume {Γ = ∅} a1)
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

