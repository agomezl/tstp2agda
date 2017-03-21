
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
a₁ = ((p ∧ q) ∨ (p ∧ r))


-- Premise
Γ : Ctxt
Γ = [ a1 ]

-- Conjecture
goal : Prop
goal = (p ∧ (q ∨ r))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = p


subgoal₁ : Prop
subgoal₁ = ((p ∧ ¬ q) ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p : Set} → ¬ p)
      atp-canonicalize $  -- Γ ⊢ ¬ p
        atp-strip $  -- Γ ⊢ p
          assume {Γ = Γ} $  -- Γ ⊢ ¬ p
            atp-neg subgoal₀

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
      ∧-proj₁ $ -- 1: ((p ∧ (p ∨ q)) ∧ (p ∨ r))
        ? -- inference rule no supported yet $  -- Γ ⊢ (((p ∧ (p ∨ q)) ∧ (p ∨ r)) ∧ (q ∨ r))
          atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∨ (p ∧ r))
            weaken (atp-neg subgoal₁) $
              (assume {Γ = ∅} a1)

