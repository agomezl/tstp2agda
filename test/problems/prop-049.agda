
-- tstp2agda proof

open import Data.FOL.Deep 5 public
open import Data.FOL.Deep.ATP.Metis 5 public

-- Vars
p1 : Prop
p1 = Var (# 0)

p2 : Prop
p2 = Var (# 1)

q1 : Prop
q1 = Var (# 2)

q2 : Prop
q2 = Var (# 3)

r : Prop
r = Var (# 4)

-- Axioms
a₁ : Prop
a₁ = (p1 ∧ p2)


a₂ : Prop
a₂ = ((q1 ∧ q2) ∧ r)


-- Premises
Γ : Ctxt
Γ = ∅ , a1 , a2

-- Conjecture
goal : Prop
goal = ((p1 ∧ q2) ∧ r)


-- Subgoals
subgoal₀ : Prop
subgoal₀ = p1


subgoal₁ : Prop
subgoal₁ = (p1 ⇒ q2)


subgoal₂ : Prop
subgoal₂ = ((p1 ∧ q2) ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ¬ p1
            atp-strip $  -- Γ ⊢ p1
              assume {Γ = Γ} $  -- Γ ⊢ ¬ p1
                atp-neg subgoal₀
          )
          (
          ∧-proj₁ $ -- 3: p1
            atp-canonicalize $  -- Γ ⊢ (p1 ∧ p2)
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
          atp-canonicalize $  -- Γ ⊢ (¬ q2 ∧ p1)
            atp-strip $  -- Γ ⊢ (p1 ⇒ q2)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ (p1 ⇒ q2)
                atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (q1 ∧ q2)
              atp-canonicalize $  -- Γ ⊢ ((q1 ∧ q2) ∧ r)
                weaken (atp-neg subgoal₁) $
                  (assume {Γ = ∅} a2)
            )
            (
            ∧-proj₁ $ -- 3: p1
              atp-canonicalize $  -- Γ ⊢ (p1 ∧ p2)
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
          atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ p1) ∧ q2)
            atp-strip $  -- Γ ⊢ ((p1 ∧ q2) ⇒ r)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ ((p1 ∧ q2) ⇒ r)
                atp-neg subgoal₂
          )
          (
          ∧-intro
            (
            ∧-proj₂ $ -- (r ≟ r)
              atp-canonicalize $  -- Γ ⊢ ((q1 ∧ q2) ∧ r)
                weaken (atp-neg subgoal₂) $
                  (assume {Γ = ∅} a2)
            )
            (
            ∧-intro
              (
              ∧-proj₁ $ -- 3: p1
                atp-canonicalize $  -- Γ ⊢ (p1 ∧ p2)
                  weaken (atp-neg subgoal₂) $
                    (assume {Γ = ∅} a1)
              )
              (
              ∧-proj₁ $ -- 1: (q1 ∧ q2)
                atp-canonicalize $  -- Γ ⊢ ((q1 ∧ q2) ∧ r)
                  weaken (atp-neg subgoal₂) $
                    (assume {Γ = ∅} a2)
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

