
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

-- Axioms
a₁ : Prop
a₁ = x


a₁ : Prop
a₁ = y


a₁ : Prop
a₁ = z


-- Premises
Γ : Ctxt
Γ = ∅ , a1 , a1 , a1

-- Conjecture
goal : Prop
goal = ((x ∨ y) ∨ z)


-- Subgoal
subgoal₀ : Prop
subgoal₀ = ((¬ x ∧ ¬ y) ⇒ z)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ((¬ x ∧ ¬ y) ∧ ¬ z)
            atp-strip $  -- Γ ⊢ ((¬ x ∧ ¬ y) ⇒ z)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ ((¬ x ∧ ¬ y) ⇒ z)
                atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-canonicalize $  -- Γ ⊢ x
              weaken (atp-neg subgoal₀) $
                (assume {Γ = ∅} a1)
            )
            (
            ∧-intro
              (
              atp-canonicalize $  -- Γ ⊢ y
                weaken (atp-neg subgoal₀) $
                  (assume {Γ = ∅} a1)
              )
              (
              atp-canonicalize $  -- Γ ⊢ z
                weaken (atp-neg subgoal₀) $
                  (assume {Γ = ∅} a1)
              )
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

