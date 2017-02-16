
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

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = (((p ∨ q) ⇒ (p ∨ r)) ⇒ (p ∨ (q ⇒ r)))


-- Subgoal
subgoal₀ : Prop
subgoal₀ = (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
  -- Γ , ¬ subgoal₀⊢ ⊥
    atp-canonicalize $
      atp-simplify $
        ∧-intro
          (
          atp-conjunct $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
                    atp-neg subgoal₀
            )
            (
            ∧-intro
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₀
              )
              (
              ∧-intro
                (
                atp-conjunct $
                  atp-canonicalize $
                    atp-strip $
                      assume {Γ = Γ} $
                        atp-neg subgoal₀
                )
                (
                atp-conjunct $
                  atp-canonicalize $
                    atp-strip $
                      assume {Γ = Γ} $
                        atp-neg subgoal₀
                )
              )
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

