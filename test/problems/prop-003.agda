
-- tstp2agda proof

open import Data.FOL.Deep 3 public
open import Data.FOL.Deep.ATP.Metis 3 public

-- Vars
x : Prop
x = Var (# 0)

y : Prop
y = Var (# 1)

z : Prop
z = Var (# 2)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = ((x ⇒ (y ⇒ z)) ⇒ ((x ⇒ y) ⇒ (x ⇒ z)))


-- Subgoal
subgoal₀ : Prop
subgoal₀ = ((((x ⇒ (y ⇒ z)) ∧ (x ⇒ y)) ∧ x) ⇒ z)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-conjunct $  -- Γ ⊢ ((¬ x ∨ ¬ y) ∨ z)
            atp-canonicalize $  -- Γ ⊢ (((¬ z ∧ x) ∧ (¬ x ∨ y)) ∧ ((¬ x ∨ ¬ y) ∨ z))
              atp-strip $  -- Γ ⊢ ((((x ⇒ (y ⇒ z)) ∧ (x ⇒ y)) ∧ x) ⇒ z)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((x ⇒ (y ⇒ z)) ∧ (x ⇒ y)) ∧ x) ⇒ z)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-conjunct $  -- Γ ⊢ x
              atp-canonicalize $  -- Γ ⊢ (((¬ z ∧ x) ∧ (¬ x ∨ y)) ∧ ((¬ x ∨ ¬ y) ∨ z))
                atp-strip $  -- Γ ⊢ ((((x ⇒ (y ⇒ z)) ∧ (x ⇒ y)) ∧ x) ⇒ z)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((x ⇒ (y ⇒ z)) ∧ (x ⇒ y)) ∧ x) ⇒ z)
                    atp-neg subgoal₀
            )
            (
            ∧-intro
              (
              atp-simplify $  -- Γ ⊢ y
                ∧-intro
                  (
                  atp-conjunct $  -- Γ ⊢ (¬ x ∨ y)
                    atp-canonicalize $  -- Γ ⊢ (((¬ z ∧ x) ∧ (¬ x ∨ y)) ∧ ((¬ x ∨ ¬ y) ∨ z))
                      atp-strip $  -- Γ ⊢ ((((x ⇒ (y ⇒ z)) ∧ (x ⇒ y)) ∧ x) ⇒ z)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((x ⇒ (y ⇒ z)) ∧ (x ⇒ y)) ∧ x) ⇒ z)
                          atp-neg subgoal₀
                  )
                  (
                  atp-conjunct $  -- Γ ⊢ x
                    atp-canonicalize $  -- Γ ⊢ (((¬ z ∧ x) ∧ (¬ x ∨ y)) ∧ ((¬ x ∨ ¬ y) ∨ z))
                      atp-strip $  -- Γ ⊢ ((((x ⇒ (y ⇒ z)) ∧ (x ⇒ y)) ∧ x) ⇒ z)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((x ⇒ (y ⇒ z)) ∧ (x ⇒ y)) ∧ x) ⇒ z)
                          atp-neg subgoal₀
                  )
              )
              (
              atp-conjunct $  -- Γ ⊢ ¬ z
                atp-canonicalize $  -- Γ ⊢ (((¬ z ∧ x) ∧ (¬ x ∨ y)) ∧ ((¬ x ∨ ¬ y) ∨ z))
                  atp-strip $  -- Γ ⊢ ((((x ⇒ (y ⇒ z)) ∧ (x ⇒ y)) ∧ x) ⇒ z)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((x ⇒ (y ⇒ z)) ∧ (x ⇒ y)) ∧ x) ⇒ z)
                      atp-neg subgoal₀
              )
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

