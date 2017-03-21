
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

-- Axioms
a₁ : Prop
a₁ = (p ⇒ q)


a₂ : Prop
a₂ = (q ⇒ r)


-- Premises
Γ : Ctxt
Γ = ∅ , a1 , a2

-- Conjecture
goal : Prop
goal = (p ⇒ r)


-- Subgoal
subgoal₀ : Prop
subgoal₀ = (p ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ q r : Set} → ¬ q ∨ r)
      atp-canonicalize $  -- Γ ⊢ (¬ q ∨ r)
        weaken (atp-neg subgoal₀) $
          (assume {Γ = ∅} a2)

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p q : Set} → ¬ p ∨ q)
      atp-canonicalize $  -- Γ ⊢ (¬ p ∨ q)
        weaken (atp-neg subgoal₁) $
          (assume {Γ = ∅} a1)

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
      ∧-proj₂ $ -- (p ≟ p)
        atp-canonicalize $  -- Γ ⊢ (¬ r ∧ p)
          atp-strip $  -- Γ ⊢ (p ⇒ r)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ r)
              atp-neg subgoal₂

