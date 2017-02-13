
-- tstp2agda proof

open import Data.FOL.Deep 3
open import Data.FOL.Deep.ATP.Metis 3

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
goal = ((x ⇒ y) ⇒ (¬ (y ∨ z) ⇒ ¬ (x ∨ z)))

-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((x ⇒ y) ∧ ¬ (y ∨ z)) ⇒ ¬ x)

subgoal₁ : Prop
subgoal₁ = ((((x ⇒ y) ∧ ¬ (y ∨ z)) ∧ ¬ x) ⇒ ¬ z)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₀
        )
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₀
        )
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₀
        )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $
      atp-canonicalize $
        atp-strip $
          assume {Γ = Γ} $
            atp-neg subgoal₁

proof : Γ ⊢ goal
proof = ? -- Not supported yet

