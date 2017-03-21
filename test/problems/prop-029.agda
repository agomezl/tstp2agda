
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

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)


-- Subgoal
subgoal₀ : Prop
subgoal₀ = ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ ¬ r)
      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
              atp-neg subgoal₀

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
              atp-neg subgoal₁

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ r ∨ q)
      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
              atp-neg subgoal₂

proof₃ : Γ ⊢ subgoal₃
proof₃ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ q ∨ r)
      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
              atp-neg subgoal₃

proof₄ : Γ ⊢ subgoal₄
proof₄ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
              atp-neg subgoal₄

proof₅ : Γ ⊢ subgoal₅
proof₅ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
              atp-neg subgoal₅

