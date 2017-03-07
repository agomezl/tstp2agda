
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
a₁ = ((p ⇒ q) ⇒ p)


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
    atp-canonicalize $  -- Γ ⊢ ({ p : Set} → ¬ p)
      ∧-proj₁ $ -- 5: ¬ p
        atp-canonicalize $  -- Γ ⊢ (¬ p ∧ q)
          atp-strip $  -- Γ ⊢ (q ⇒ p)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ (q ⇒ p)
              atp-neg subgoal₀

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
      ∧-proj₁ $ -- 3: p
        ? -- inference rule no supported yet $  -- Γ ⊢ (p ∧ (¬ q ∨ p))
          atp-canonicalize $  -- Γ ⊢ (p ∨ (¬ q ∧ p))
            weaken (atp-neg subgoal₁) $
              (assume {Γ = ∅} a1)

