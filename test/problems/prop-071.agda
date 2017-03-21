
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
a₁ = (p ∧ (q ∨ r))


-- Premise
Γ : Ctxt
Γ = [ a1 ]

-- Conjecture
goal : Prop
goal = ((p ∧ q) ∨ (p ∧ r))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (¬ (p ∧ q) ⇒ p)


subgoal₁ : Prop
subgoal₁ = ((¬ (p ∧ q) ∧ p) ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ (¬ p ∧ (¬ p ∨ ¬ q))
            atp-strip $  -- Γ ⊢ (¬ (p ∧ q) ⇒ p)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ (¬ (p ∧ q) ⇒ p)
                atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 3: p
              atp-canonicalize $  -- Γ ⊢ (p ∧ (q ∨ r))
                weaken (atp-neg subgoal₀) $
                  (assume {Γ = ∅} a1)
            )
            (
            ∧-proj₁ $ -- 3: p
              atp-canonicalize $  -- Γ ⊢ (p ∧ (q ∨ r))
                weaken (atp-neg subgoal₀) $
                  (assume {Γ = ∅} a1)
            )
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p) ∧ (¬ p ∨ ¬ q))
            atp-strip $  -- Γ ⊢ ((¬ (p ∧ q) ∧ p) ⇒ r)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ ((¬ (p ∧ q) ∧ p) ⇒ r)
                atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            ∧-proj₂ $ -- ((q ∨ r) ≟ (q ∨ r))
              atp-canonicalize $  -- Γ ⊢ (p ∧ (q ∨ r))
                weaken (atp-neg subgoal₁) $
                  (assume {Γ = ∅} a1)
            )
            (
            ∧-intro
              (
              ∧-proj₁ $ -- 3: p
                atp-canonicalize $  -- Γ ⊢ (p ∧ (q ∨ r))
                  weaken (atp-neg subgoal₁) $
                    (assume {Γ = ∅} a1)
              )
              (
              ∧-proj₁ $ -- 3: p
                atp-canonicalize $  -- Γ ⊢ (p ∧ (q ∨ r))
                  weaken (atp-neg subgoal₁) $
                    (assume {Γ = ∅} a1)
              )
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    (
    ∧-intro
      subgoal₀
      subgoal₁
    )

