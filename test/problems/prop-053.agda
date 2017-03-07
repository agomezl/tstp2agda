
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
a₁ = ((p ⇒ q) ⇒ (p ⇒ r))


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
    atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
      ? -- inference rule no supported yet $  -- Γ ⊢ ((¬ p ∨ ¬ q) ∨ r)
        atp-canonicalize $  -- Γ ⊢ ((¬ p ∨ r) ∨ (¬ q ∧ p))
          weaken (atp-neg subgoal₀) $
            (assume {Γ = ∅} a1)

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
      ∧-proj₁ $ -- 1: (¬ r ∧ p)
        atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p) ∧ q)
          atp-strip $  -- Γ ⊢ ((q ∧ p) ⇒ r)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((q ∧ p) ⇒ r)
              atp-neg subgoal₁

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    id -- resolve 4.
      (
              atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
          ∧-proj₁ $ -- 1: (¬ r ∧ p)
            atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p) ∧ q)
              atp-strip $  -- Γ ⊢ ((q ∧ p) ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((q ∧ p) ⇒ r)
                  atp-neg subgoal₂
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
          ? -- inference rule no supported yet $  -- Γ ⊢ ((¬ p ∨ ¬ q) ∨ r)
            atp-canonicalize $  -- Γ ⊢ ((¬ p ∨ r) ∨ (¬ q ∧ p))
              weaken (atp-neg subgoal₂) $
                (assume {Γ = ∅} a1)
      )

proof₃ : Γ ⊢ subgoal₃
proof₃ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ q : Set} → q)
      ∧-proj₂ $ -- (q ≟ q)
        atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p) ∧ q)
          atp-strip $  -- Γ ⊢ ((q ∧ p) ⇒ r)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((q ∧ p) ⇒ r)
              atp-neg subgoal₃

proof₄ : Γ ⊢ subgoal₄
proof₄ =
  RAA $
    id -- resolve 4.
      (
              atp-canonicalize $  -- Γ ⊢ ({ q : Set} → q)
          ∧-proj₂ $ -- (q ≟ q)
            atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p) ∧ q)
              atp-strip $  -- Γ ⊢ ((q ∧ p) ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((q ∧ p) ⇒ r)
                  atp-neg subgoal₄
      )
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
              ∧-proj₁ $ -- 1: (¬ r ∧ p)
                atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p) ∧ q)
                  atp-strip $  -- Γ ⊢ ((q ∧ p) ⇒ r)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((q ∧ p) ⇒ r)
                      atp-neg subgoal₄
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
              ? -- inference rule no supported yet $  -- Γ ⊢ ((¬ p ∨ ¬ q) ∨ r)
                atp-canonicalize $  -- Γ ⊢ ((¬ p ∨ r) ∨ (¬ q ∧ p))
                  weaken (atp-neg subgoal₄) $
                    (assume {Γ = ∅} a1)
          )
      )

proof₅ : Γ ⊢ subgoal₅
proof₅ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ r : Set} → ¬ r)
      ∧-proj₁ $ -- 1: (¬ r ∧ p)
        atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p) ∧ q)
          atp-strip $  -- Γ ⊢ ((q ∧ p) ⇒ r)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((q ∧ p) ⇒ r)
              atp-neg subgoal₅

proof₆ : Γ ⊢ subgoal₆
proof₆ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ q : Set} → q)
              ∧-proj₂ $ -- (q ≟ q)
                atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p) ∧ q)
                  atp-strip $  -- Γ ⊢ ((q ∧ p) ⇒ r)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((q ∧ p) ⇒ r)
                      atp-neg subgoal₆
          )
          (
                      id -- resolve 4.
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
                  ∧-proj₁ $ -- 1: (¬ r ∧ p)
                    atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p) ∧ q)
                      atp-strip $  -- Γ ⊢ ((q ∧ p) ⇒ r)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((q ∧ p) ⇒ r)
                          atp-neg subgoal₆
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
                  ? -- inference rule no supported yet $  -- Γ ⊢ ((¬ p ∨ ¬ q) ∨ r)
                    atp-canonicalize $  -- Γ ⊢ ((¬ p ∨ r) ∨ (¬ q ∧ p))
                      weaken (atp-neg subgoal₆) $
                        (assume {Γ = ∅} a1)
              )
          )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ r : Set} → ¬ r)
          ∧-proj₁ $ -- 1: (¬ r ∧ p)
            atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p) ∧ q)
              atp-strip $  -- Γ ⊢ ((q ∧ p) ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((q ∧ p) ⇒ r)
                  atp-neg subgoal₆
      )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

