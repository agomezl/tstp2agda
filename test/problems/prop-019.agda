
-- tstp2agda proof

open import Data.FOL.Deep 2
open import Data.FOL.Deep.ATP.Metis 2

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ ¬ (¬ q ∨ ¬ q))

-- Subgoals
subgoal₀ : Prop
subgoal₀ = ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ q)

subgoal₁ : Prop
subgoal₁ = (((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ∧ ¬ ¬ q) ⇒ q)

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

