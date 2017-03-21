
-- tstp2agda proof

open import Data.FOL.Deep 3 public
open import Data.FOL.Deep.ATP.Metis 3 public

-- Vars
a : Prop
a = Var (# 0)

b : Prop
b = Var (# 1)

z : Prop
z = Var (# 2)

-- Axioms
a₁ : Prop
a₁ = a


a₂ : Prop
a₂ = b


a₃ : Prop
a₃ = ((a ∧ b) ⇒ z)


-- Premises
Γ : Ctxt
Γ = ∅ , a1 , a2 , a3

-- Conjecture
a₄ : Prop
a₄ = z


-- Subgoal
subgoal₀ : Prop
subgoal₀ = z

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ¬ z
            atp-strip $  -- Γ ⊢ z
              assume {Γ = Γ} $  -- Γ ⊢ ¬ z
                atp-neg subgoal₀
          )
          (
          atp-simplify $  -- Γ ⊢ z
            ∧-intro
              (
              atp-canonicalize $  -- Γ ⊢ ((¬ a ∨ ¬ b) ∨ z)
                weaken (atp-neg subgoal₀) $
                  (assume {Γ = ∅} a3)
              )
              (
              ∧-intro
                (
                atp-canonicalize $  -- Γ ⊢ a
                  weaken (atp-neg subgoal₀) $
                    (assume {Γ = ∅} a1)
                )
                (
                atp-canonicalize $  -- Γ ⊢ b
                  weaken (atp-neg subgoal₀) $
                    (assume {Γ = ∅} a2)
                )
              )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

