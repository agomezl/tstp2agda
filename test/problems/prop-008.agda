
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
                  atp-conjunct $
                    atp-canonicalize $
                      atp-strip $
                        assume {Γ = Γ} $
                          atp-neg subgoal₀
                  )
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

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

