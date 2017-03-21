
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
a₁ = ((p ∧ q) ∧ r)


-- Premise
Γ : Ctxt
Γ = [ a1 ]

-- Conjecture
goal : Prop
goal = ((r ∧ p) ∧ q)


-- Subgoals
subgoal₀ : Prop
subgoal₀ = r


subgoal₁ : Prop
subgoal₁ = (r ⇒ p)


subgoal₂ : Prop
subgoal₂ = ((r ∧ p) ⇒ q)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ¬ r
            atp-strip $  -- Γ ⊢ r
              assume {Γ = Γ} $  -- Γ ⊢ ¬ r
                atp-neg subgoal₀
          )
          (
          ∧-proj₂ $ -- (r ≟ r)
            atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ r)
              weaken (atp-neg subgoal₀) $
                (assume {Γ = ∅} a1)
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ (¬ p ∧ r)
            atp-strip $  -- Γ ⊢ (r ⇒ p)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ (r ⇒ p)
                atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (p ∧ q)
              atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ r)
                weaken (atp-neg subgoal₁) $
                  (assume {Γ = ∅} a1)
            )
            (
            ∧-proj₂ $ -- (r ≟ r)
              atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ r)
                weaken (atp-neg subgoal₁) $
                  (assume {Γ = ∅} a1)
            )
          )

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ p) ∧ r)
            atp-strip $  -- Γ ⊢ ((r ∧ p) ⇒ q)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ ((r ∧ p) ⇒ q)
                atp-neg subgoal₂
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (p ∧ q)
              atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ r)
                weaken (atp-neg subgoal₂) $
                  (assume {Γ = ∅} a1)
            )
            (
            ∧-intro
              (
              ∧-proj₁ $ -- 1: (p ∧ q)
                atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ r)
                  weaken (atp-neg subgoal₂) $
                    (assume {Γ = ∅} a1)
              )
              (
              ∧-proj₂ $ -- (r ≟ r)
                atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ r)
                  weaken (atp-neg subgoal₂) $
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
      (
      ∧-intro
        subgoal₁
        subgoal₂
      )
    )

