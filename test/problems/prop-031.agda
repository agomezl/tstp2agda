
-- tstp2agda proof

open import Data.FOL.Deep 3
open import Data.FOL.Deep.ATP.Metis 3

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
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        atp-canonicalize $
          atp-strip $
            assume {Γ = Γ} $
              atp-neg subgoal₀
        )
        (
        atp-simplify $ ∧-intro
          (
          atp-canonicalize $
            weaken (atp-neg subgoal₀) (assume {Γ = ∅} a3)
          )
          (
          atp-canonicalize $
            weaken (atp-neg subgoal₀) (assume {Γ = ∅} a1)
          )
          (
          atp-canonicalize $
            weaken (atp-neg subgoal₀) (assume {Γ = ∅} a2)
          )
        )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀
