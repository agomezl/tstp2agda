
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

proof₆ : Γ ⊢ subgoal₆
proof₆ =
  RAA $
    id -- resolve 4.
      (
              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
          ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                  atp-neg subgoal₆
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                  atp-neg subgoal₆
      )

proof₇ : Γ ⊢ subgoal₇
proof₇ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
              atp-neg subgoal₇

proof₈ : Γ ⊢ subgoal₈
proof₈ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
              atp-neg subgoal₈

proof₉ : Γ ⊢ subgoal₉
proof₉ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                      atp-neg subgoal₉
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                      atp-neg subgoal₉
          )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                  atp-neg subgoal₉
      )

proof₁₀ : Γ ⊢ subgoal₁₀
proof₁₀ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                  ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₀
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₀
              )
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                      atp-neg subgoal₁₀
          )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                  atp-neg subgoal₁₀
      )

proof₁₁ : Γ ⊢ subgoal₁₁
proof₁₁ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                      atp-neg subgoal₁₁
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                      atp-neg subgoal₁₁
          )
      )
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₁
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₁
                  )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₁
              )
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                      atp-neg subgoal₁₁
          )
      )

proof₁₂ : Γ ⊢ subgoal₁₂
proof₁₂ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                  ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₂
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₂
              )
          )
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                          ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₂
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₂
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₂
                  )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₂
              )
          )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ q ∨ r)
          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                  atp-neg subgoal₁₂
      )

proof₁₃ : Γ ⊢ subgoal₁₃
proof₁₃ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₃
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₃
                  )
              )
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₃
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₃
                          )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₃
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₃
                  )
              )
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ q ∨ r)
              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                      atp-neg subgoal₁₃
          )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ r ∨ q)
          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                  atp-neg subgoal₁₃
      )

proof₁₄ : Γ ⊢ subgoal₁₄
proof₁₄ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                  ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₄
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₄
              )
          )
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                          ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₄
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₄
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₄
                  )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₄
              )
          )
      )
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                          ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₄
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₄
                      )
                  )
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      id -- resolve 4.
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                  ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₄
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₄
                              )
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₄
                          )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₄
                      )
                  )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ q ∨ r)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₄
              )
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ r ∨ q)
              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                      atp-neg subgoal₁₄
          )
      )

proof₁₅ : Γ ⊢ subgoal₁₅
proof₁₅ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₅
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₅
                  )
              )
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₅
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₅
                          )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₅
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₅
                  )
              )
          )
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₅
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₅
                          )
                      )
                      (
                                              id -- resolve 4.
                          (
                                                      id -- resolve 4.
                              (
                                                              id -- resolve 4.
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₅
                                  )
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₅
                                  )
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₅
                              )
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₅
                          )
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ q ∨ r)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₅
                  )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ r ∨ q)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₅
              )
          )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                  atp-neg subgoal₁₅
      )

proof₁₆ : Γ ⊢ subgoal₁₆
proof₁₆ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                  ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₆
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₆
              )
          )
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                          ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₆
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₆
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₆
                  )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₆
              )
          )
      )
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                          ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₆
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₆
                      )
                  )
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      id -- resolve 4.
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                  ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₆
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₆
                              )
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₆
                          )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₆
                      )
                  )
              )
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      id -- resolve 4.
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                  ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₆
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₆
                              )
                          )
                          (
                                                      id -- resolve 4.
                              (
                                                              id -- resolve 4.
                                  (
                                                                      id -- resolve 4.
                                      (
                                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                          ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                  atp-neg subgoal₁₆
                                      )
                                      (
                                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                  atp-neg subgoal₁₆
                                      )
                                  )
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₆
                                  )
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₆
                              )
                          )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ q ∨ r)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₆
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ r ∨ q)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₆
                  )
              )
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                      atp-neg subgoal₁₆
          )
      )

proof₁₇ : Γ ⊢ subgoal₁₇
proof₁₇ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₇
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₇
                  )
              )
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₇
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₇
                          )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₇
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₇
                  )
              )
          )
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₇
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₇
                          )
                      )
                      (
                                              id -- resolve 4.
                          (
                                                      id -- resolve 4.
                              (
                                                              id -- resolve 4.
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₇
                                  )
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₇
                                  )
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₇
                              )
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₇
                          )
                      )
                  )
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      id -- resolve 4.
                              (
                                                              id -- resolve 4.
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₇
                                  )
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₇
                                  )
                              )
                              (
                                                              id -- resolve 4.
                                  (
                                                                      id -- resolve 4.
                                      (
                                                                              id -- resolve 4.
                                          (
                                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                      atp-neg subgoal₁₇
                                          )
                                          (
                                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                      atp-neg subgoal₁₇
                                          )
                                      )
                                      (
                                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                  atp-neg subgoal₁₇
                                      )
                                  )
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₇
                                  )
                              )
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ q ∨ r)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₇
                          )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ r ∨ q)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₇
                      )
                  )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₇
              )
          )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ ¬ r)
          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                  atp-neg subgoal₁₇
      )

proof₁₈ : Γ ⊢ subgoal₁₈
proof₁₈ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                  ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₈
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₈
              )
          )
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                          ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₈
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₈
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₈
                  )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₈
              )
          )
      )
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                          ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₈
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₈
                      )
                  )
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      id -- resolve 4.
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                  ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₈
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₈
                              )
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₈
                          )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₈
                      )
                  )
              )
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      id -- resolve 4.
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                  ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₈
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₈
                              )
                          )
                          (
                                                      id -- resolve 4.
                              (
                                                              id -- resolve 4.
                                  (
                                                                      id -- resolve 4.
                                      (
                                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                          ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                  atp-neg subgoal₁₈
                                      )
                                      (
                                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                  atp-neg subgoal₁₈
                                      )
                                  )
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₈
                                  )
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₈
                              )
                          )
                      )
                      (
                                              id -- resolve 4.
                          (
                                                      id -- resolve 4.
                              (
                                                              id -- resolve 4.
                                  (
                                                                      id -- resolve 4.
                                      (
                                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                          ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                  atp-neg subgoal₁₈
                                      )
                                      (
                                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                  atp-neg subgoal₁₈
                                      )
                                  )
                                  (
                                                                      id -- resolve 4.
                                      (
                                                                              id -- resolve 4.
                                          (
                                                                                      id -- resolve 4.
                                              (
                                                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                                  ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                          atp-neg subgoal₁₈
                                              )
                                              (
                                                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                          atp-neg subgoal₁₈
                                              )
                                          )
                                          (
                                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                      atp-neg subgoal₁₈
                                          )
                                      )
                                      (
                                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                  atp-neg subgoal₁₈
                                      )
                                  )
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ q ∨ r)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₈
                              )
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ r ∨ q)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₈
                          )
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₈
                  )
              )
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ ¬ r)
              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                      atp-neg subgoal₁₈
          )
      )

proof₁₉ : Γ ⊢ subgoal₁₉
proof₁₉ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₉
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₉
                  )
              )
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₉
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₉
                          )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₉
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₉
                  )
              )
          )
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₉
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₉
                          )
                      )
                      (
                                              id -- resolve 4.
                          (
                                                      id -- resolve 4.
                              (
                                                              id -- resolve 4.
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₉
                                  )
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₉
                                  )
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₉
                              )
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₉
                          )
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ q ∨ r)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₉
                  )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ r ∨ q)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₉
              )
          )
      )
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₉
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₉
                  )
              )
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₉
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₉
                          )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₉
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                              atp-neg subgoal₁₉
                  )
              )
          )
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₉
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₉
                          )
                      )
                      (
                                              id -- resolve 4.
                          (
                                                      id -- resolve 4.
                              (
                                                              id -- resolve 4.
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₉
                                  )
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₉
                                  )
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₉
                              )
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                      atp-neg subgoal₁₉
                          )
                      )
                  )
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      id -- resolve 4.
                              (
                                                              id -- resolve 4.
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₉
                                  )
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₉
                                  )
                              )
                              (
                                                              id -- resolve 4.
                                  (
                                                                      id -- resolve 4.
                                      (
                                                                              id -- resolve 4.
                                          (
                                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                      atp-neg subgoal₁₉
                                          )
                                          (
                                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                      atp-neg subgoal₁₉
                                          )
                                      )
                                      (
                                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                  atp-neg subgoal₁₉
                                      )
                                  )
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₉
                                  )
                              )
                          )
                          (
                                                      id -- resolve 4.
                              (
                                                              id -- resolve 4.
                                  (
                                                                      id -- resolve 4.
                                      (
                                                                              id -- resolve 4.
                                          (
                                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                              ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                      atp-neg subgoal₁₉
                                          )
                                          (
                                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                      atp-neg subgoal₁₉
                                          )
                                      )
                                      (
                                                                              id -- resolve 4.
                                          (
                                                                                      id -- resolve 4.
                                              (
                                                                                              id -- resolve 4.
                                                  (
                                                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → p ∨ q ∨ r)
                                                      ∧-proj₂ $ -- (((p ∨ q) ∨ r) ≟ ((p ∨ q) ∨ r))
                                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                              atp-neg subgoal₁₉
                                                  )
                                                  (
                                                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ r ∨ p ∨ q)
                                                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                              atp-neg subgoal₁₉
                                                  )
                                              )
                                              (
                                                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ p ∨ r)
                                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                          atp-neg subgoal₁₉
                                              )
                                          )
                                          (
                                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ q ∨ ¬ r ∨ p)
                                              ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                                atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                                  atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                                      atp-neg subgoal₁₉
                                          )
                                      )
                                  )
                                  (
                                                                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ q ∨ r)
                                      ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                        atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                          atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                              atp-neg subgoal₁₉
                                  )
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ r ∨ q)
                                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                          atp-neg subgoal₁₉
                              )
                          )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
                          ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                            atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                              atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                                  atp-neg subgoal₁₉
                      )
                  )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ ¬ r)
                  ∧-proj₁ $ -- 1: ((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((((((((¬ p ∨ ¬ q) ∨ ¬ r) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ q)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ q ∨ ¬ r) ∨ p)) ∧ ((¬ q ∨ p) ∨ r)) ∧ ((¬ r ∨ p) ∨ q)) ∧ ((p ∨ q) ∨ r))
                      atp-strip $  -- Γ ⊢ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((((((p ∨ q) ∨ r) ∧ ((p ∨ q) ∨ ¬ r)) ∧ ((p ∨ ¬ q) ∨ r)) ∧ ((p ∨ ¬ q) ∨ ¬ r)) ∧ ((¬ p ∨ q) ∨ r)) ∧ ((¬ p ∨ q) ∨ ¬ r)) ∧ ((¬ p ∨ ¬ q) ∨ r)) ∧ ((¬ p ∨ ¬ q) ∨ ¬ r)) ⇒ ⊥)
                          atp-neg subgoal₁₉
              )
          )
      )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

