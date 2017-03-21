
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
axiomp : Prop
axiomp = (q ∧ p)


axiomq : Prop
axiomq = r


-- Premises
Γ : Ctxt
Γ = ∅ , axiomp , axiomq

-- Conjecture
goal : Prop
goal = ((p ∧ r) ∧ q)


-- Subgoals
subgoal₀ : Prop
subgoal₀ = p


subgoal₁ : Prop
subgoal₁ = (p ⇒ r)


subgoal₂ : Prop
subgoal₂ = ((p ∧ r) ⇒ q)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ¬ p
            atp-strip $  -- Γ ⊢ p
              assume {Γ = Γ} $  -- Γ ⊢ ¬ p
                atp-neg subgoal₀
          )
          (
          ∧-proj₁ $ -- 3: p
            atp-canonicalize $  -- Γ ⊢ (p ∧ q)
              weaken (atp-neg subgoal₀) $
                (assume {Γ = ∅} axiomp)
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ (¬ r ∧ p)
            atp-strip $  -- Γ ⊢ (p ⇒ r)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ r)
                atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            atp-canonicalize $  -- Γ ⊢ r
              weaken (atp-neg subgoal₁) $
                (assume {Γ = ∅} axiomq)
            )
            (
            ∧-proj₁ $ -- 3: p
              atp-canonicalize $  -- Γ ⊢ (p ∧ q)
                weaken (atp-neg subgoal₁) $
                  (assume {Γ = ∅} axiomp)
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
            atp-strip $  -- Γ ⊢ ((p ∧ r) ⇒ q)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ ((p ∧ r) ⇒ q)
                atp-neg subgoal₂
          )
          (
          ∧-intro
            (
            ∧-proj₂ $ -- (q ≟ q)
              atp-canonicalize $  -- Γ ⊢ (p ∧ q)
                weaken (atp-neg subgoal₂) $
                  (assume {Γ = ∅} axiomp)
            )
            (
            ∧-intro
              (
              ∧-proj₁ $ -- 3: p
                atp-canonicalize $  -- Γ ⊢ (p ∧ q)
                  weaken (atp-neg subgoal₂) $
                    (assume {Γ = ∅} axiomp)
              )
              (
              atp-canonicalize $  -- Γ ⊢ r
                weaken (atp-neg subgoal₂) $
                  (assume {Γ = ∅} axiomq)
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

