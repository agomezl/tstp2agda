
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
a₁ = (p ∨ (q ∧ r))


-- Premise
Γ : Ctxt
Γ = [ a1 ]

-- Conjecture
goal : Prop
goal = ((p ∨ q) ∧ (p ∨ r))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (¬ p ⇒ q)


subgoal₁ : Prop
subgoal₁ = (((p ∨ q) ∧ ¬ p) ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p q : Set} → p ∨ q)
      ∧-proj₁ $ -- 1: (p ∨ q)
        ? -- inference rule no supported yet $  -- Γ ⊢ ((p ∨ q) ∧ (p ∨ r))
          atp-canonicalize $  -- Γ ⊢ (p ∨ (q ∧ r))
            weaken (atp-neg subgoal₀) $
              (assume {Γ = ∅} a1)

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p : Set} → ¬ p)
      ∧-proj₁ $ -- 5: ¬ p
        atp-canonicalize $  -- Γ ⊢ (¬ p ∧ ¬ q)
          atp-strip $  -- Γ ⊢ (¬ p ⇒ q)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ (¬ p ⇒ q)
              atp-neg subgoal₁

