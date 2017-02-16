
-- tstp2agda proof

open import Data.FOL.Deep 3 public
open import Data.FOL.Deep.ATP.Metis 3 public

-- Vars
s : Prop
s = Var (# 0)

x : Prop
x = Var (# 1)

y : Prop
y = Var (# 2)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = (((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ⇒ (s ⇒ y))


-- Subgoal
subgoal₀ : Prop
subgoal₀ = ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-conjunct $  -- Γ ⊢ ((¬ s ∨ ¬ x) ∨ y)
            atp-canonicalize $  -- Γ ⊢ (((¬ y ∧ s) ∧ (¬ s ∨ x)) ∧ ((¬ s ∨ ¬ x) ∨ y))
              atp-strip $  -- Γ ⊢ ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-conjunct $  -- Γ ⊢ s
              atp-canonicalize $  -- Γ ⊢ (((¬ y ∧ s) ∧ (¬ s ∨ x)) ∧ ((¬ s ∨ ¬ x) ∨ y))
                atp-strip $  -- Γ ⊢ ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)
                    atp-neg subgoal₀
            )
            (
            ∧-intro
              (
              atp-simplify $  -- Γ ⊢ x
                ∧-intro
                  (
                  atp-conjunct $  -- Γ ⊢ (¬ s ∨ x)
                    atp-canonicalize $  -- Γ ⊢ (((¬ y ∧ s) ∧ (¬ s ∨ x)) ∧ ((¬ s ∨ ¬ x) ∨ y))
                      atp-strip $  -- Γ ⊢ ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)
                          atp-neg subgoal₀
                  )
                  (
                  atp-conjunct $  -- Γ ⊢ s
                    atp-canonicalize $  -- Γ ⊢ (((¬ y ∧ s) ∧ (¬ s ∨ x)) ∧ ((¬ s ∨ ¬ x) ∨ y))
                      atp-strip $  -- Γ ⊢ ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)
                          atp-neg subgoal₀
                  )
              )
              (
              atp-conjunct $  -- Γ ⊢ ¬ y
                atp-canonicalize $  -- Γ ⊢ (((¬ y ∧ s) ∧ (¬ s ∨ x)) ∧ ((¬ s ∨ ¬ x) ∨ y))
                  atp-strip $  -- Γ ⊢ ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)
                      atp-neg subgoal₀
              )
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

